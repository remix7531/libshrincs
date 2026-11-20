#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# libshrincs - formally verified SHRINCS implementations.
#
# Regenerate official stateful vectors from committed reference sources.
# This manual step uses only local git objects; builds use the committed KAT.

import argparse
import csv
import hashlib
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

from gen_vectors import Writer

PINNED_COMMIT = "4fe68e3a68fd58be6b0e19436ff6fb7a3357a291"


def committed(repository, path):
    return subprocess.check_output([
        "git", "-C", str(repository), "show", f"{PINNED_COMMIT}:{path}",
    ])


def generate(repository):
    with tempfile.TemporaryDirectory(prefix="shrincs-fxmss-") as directory:
        root = Path(directory)
        for name in ("impl/shrincs.py", "gen_test_vectors.py"):
            target = root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(committed(repository, name))
        subprocess.run([sys.executable, "gen_test_vectors.py"], cwd=root, check=True)
        fingerprints = []
        for name in ("keygen.csv", "signatures_valid.csv"):
            actual = hashlib.sha256((root / "test_vectors" / name).read_bytes()).hexdigest()
            expected = committed(repository, f"test_vectors/{name}.fp").decode().strip()
            if actual != expected:
                raise ValueError(f"{name}: fingerprint {actual} differs from {expected}")
            fingerprints.append(f"# {name} SHA256 {actual}")
        with (root / "test_vectors/signatures_valid.csv").open(newline="") as source:
            rows = list(csv.DictReader(source))[:3]
        module_spec = importlib.util.spec_from_file_location("shrincs", root / "impl/shrincs.py")
        s = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(s)
        w = Writer()

        def case(label, function, fields, output):
            w.lines.append(f"# {w.count + 1:03d}: {label}")
            w.case(function, fields, output)

        def verify(label, row, signature=None, ctx=None):
            signature = bytes.fromhex(row["signature"]) if signature is None else signature
            ctx = bytes.fromhex(row["ctx"]) if ctx is None else ctx
            message, pk = bytes.fromhex(row["message"]), bytes.fromhex(row["pubkey"])
            case(label, "shrincs_sf_verify", [
                ("message", message), ("signature", signature), ("ctx", ctx), ("pubkey", pk),
            ], s.shrincs_verify(message, signature, ctx, pk))

        for number, row in enumerate(rows, 2):
            assert bytes.fromhex(row["signature"])[0] != 255
            verify(f"official signatures_valid.csv row {number}, state {row['state_ctr']}", row)
        for offset, label in ((20, "WOTS byte"), (532, "authentication byte")):
            signature = bytearray.fromhex(rows[0]["signature"])
            signature[offset] ^= 1
            verify(f"row 2 flipped {label} at offset {offset}", rows[0], bytes(signature))
        verify("row 2 wrong context", rows[0], ctx=b"\x01")

        selections = [
            (False, 1, 0), (False, 1, 1), (False, 1, 2),
            (False, 255, 254), (False, 255, 255), (False, 255, 256),
            (True, 1, 1), (True, 1, 2), (True, 64, 2**64 - 1),
            (True, 64, None),
        ]
        for balanced, depth, state in selections:
            structure = bytes([int(balanced), depth])
            selected = s.shrincs_sf_leaf_select(structure, state)
            output = "none" if selected is None else f"{selected[0]} : {selected[1]}"
            fields = [("structure", structure), ("state", "none" if state is None else str(state))]
            case(f"{'B' if balanced else 'U'}{depth} leaf at state {state}",
                 "shrincs_sf_leaf_select", fields, output)
        for balanced, depth, state in ((False, 1, 1), (False, 255, 255),
                                       (True, 1, 1), (True, 64, 2**64 - 1)):
            selected = s.shrincs_sf_leaf_select(bytes([int(balanced), depth]), state)
            case(f"{'B' if balanced else 'U'}{depth} final leaf consumes to exhaustion",
                 "shrincs_sf_consume", [("structure", bytes([int(balanced), depth])),
                 ("state", str(state))], f"none : {selected[0]} : {selected[1]}")

        sk = bytes.fromhex(rows[0]["seckey"])
        for state, ctx, label in ((None, b"", "exhausted"), (7, b"", "past U6 end"),
                                  (0, bytes(256), "context exceeds 255 bytes")):
            case(f"sign refuses {label}", "shrincs_sf_sign", [
                ("message", b"hello"), ("ctx", ctx), ("seckey", sk),
                ("state", "none" if state is None else str(state)),
            ], None)
        case("official public key extraction", "shrincs_extract_pubkey", [("seckey", sk)],
             s.shrincs_extract_pubkey(sk))

        return w, fingerprints


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shrincs-bip", default="../shrincs-bip")
    parser.add_argument("-o", "--out", required=True)
    args = parser.parse_args()
    writer, fingerprints = generate(Path(args.shrincs_bip))
    header = ["# Stateful FXMSS vectors for libshrincs.",
              f"# shrincs-bip {PINNED_COMMIT}; generated from local committed sources.",
              *fingerprints, ""]
    Path(args.out).write_text("\n".join(header + writer.lines))
    print(f"wrote {args.out}: {writer.count} cases", file=sys.stderr)


if __name__ == "__main__":
    main()
