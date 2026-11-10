#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
#
# libshrincs - formally verified SHRINCS implementations.
# Copyright (c) 2026 remix7531 <remix7531@mailbox.org>
#
# Generate the WOTS+C reference vectors (test/spec/vectors/wots_c.kat) from the
# Python reference in a shrincs-bip checkout.
#
# This is a manual developer step. The vectors are committed, so the checks
# that read them need neither Python nor a shrincs-bip checkout.
#
#     python3 test/spec/gen_vectors.py --shrincs-bip ../shrincs-bip \
#         -o test/spec/vectors/wots_c.kat
#
# The checkout must be at PINNED_COMMIT with impl/shrincs.py unmodified. Any
# other state is refused, because proof/spec.v transcribes exactly that file.

import argparse
import hashlib
import importlib.util
import subprocess
import sys
from pathlib import Path

PINNED_COMMIT = "86cfca6ddcf79da87cd9a6d0ddc388cf43176b95"
REFERENCE = "impl/shrincs.py"


def git(repository, *arguments):
    result = subprocess.run(
        ["git", "-C", str(repository), *arguments],
        capture_output=True, text=True, check=False,
    )
    if result.returncode != 0:
        sys.exit(f"git {' '.join(arguments)} failed in {repository}: {result.stderr.strip()}")
    return result.stdout.strip()


def load_reference(repository):
    head = git(repository, "rev-parse", "HEAD")
    if head != PINNED_COMMIT:
        sys.exit(f"{repository} is at {head}, but the vectors are pinned to {PINNED_COMMIT}")
    if git(repository, "status", "--porcelain", "--", REFERENCE):
        sys.exit(f"{repository}/{REFERENCE} differs from the pinned commit")
    path = Path(repository) / REFERENCE
    spec = importlib.util.spec_from_file_location("shrincs", path)
    if spec is None or spec.loader is None:
        sys.exit(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def stretch(label, length):
    """Deterministic input bytes: SHA-256 of the label and a block counter."""
    out = b""
    block = 0
    while len(out) < length:
        out += hashlib.sha256(label.encode() + block.to_bytes(4, "big")).digest()
        block += 1
    return out[:length]


class Writer:
    def __init__(self):
        self.lines = []
        self.count = 0

    def case(self, function, fields, output):
        self.lines.append(f"function = {function}")
        for name, value in fields:
            self.lines.append(f"{name} = {render(value)}")
        self.lines.append(f"output = {render_output(output)}")
        self.lines.append("")
        self.count += 1


def render(value):
    if isinstance(value, bool):
        return "1" if value else "0"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, (bytes, bytearray)):
        return bytes(value).hex() if value else "empty"
    if isinstance(value, str):
        return value
    raise TypeError(value)


def render_output(value):
    if value is None:
        return "none"
    if isinstance(value, list):
        return " ".join(str(item) for item in value)
    if isinstance(value, tuple):
        counter, indexes = value
        return f"{counter} : " + " ".join(str(item) for item in indexes)
    return render(value)


# The two leaf positions every signer-side function is run at. Together they
# take each address field to both ends of its range and both tree shapes.
LEAVES = [
    ("low", 0, 0, False, 0),
    ("high", 255, 2**64 - 1, True, 255),
]


def generate(s):
    w = Writer()

    for label, b, outlen in [("a", 4, 32), ("b", 13, 2), ("c", 1, 24), ("d", 8, 4), ("e", 7, 5)]:
        x = stretch("base_2b" + label, s.ceildiv(outlen * b, 8))
        w.case("base_2b", [("x", x), ("b", b), ("outlen", outlen)], s.base_2b(x, b, outlen))

    for label, height, index, balanced, depth in LEAVES:
        pk_seed = stretch("pk_seed" + label, 16)
        sk_seed = stretch("sk_seed" + label, 16)
        digest = stretch("digest" + label, 32)
        node = stretch("node" + label, 16)
        anchor = [("node_height", height), ("node_index", index)]
        shape = [("tree_balanced", balanced), ("tree_depth", depth)]

        w.case("F",
               [("pk_seed", pk_seed), ("height", height), ("index", index),
                ("chain_index", 31), ("hash_index", 14), ("M_1", node)],
               s.F(pk_seed, s.WotsCHash(height, index, 31, 14), node))
        w.case("PRF",
               [("pk_seed", pk_seed), ("sk_seed", sk_seed), ("height", height), ("index", index),
                ("tree_balanced", balanced), ("tree_depth", depth), ("chain_index", 17)],
               s.PRF(pk_seed, sk_seed, s.WotsCPrf(height, index, balanced, depth, 17)))
        tips = stretch("tips" + label, s.WOTS_C_CHAINS_SIZE)
        w.case("T_sf",
               [("pk_seed", pk_seed), ("height", height), ("index", index), ("M_l", tips)],
               s.T_sf(pk_seed, s.WotsCPk(height, index), tips))
        for counter in (0, 258, 65535):
            w.case("H_grind",
                   [("pk_seed", pk_seed), ("height", height), ("index", index),
                    ("digest", digest), ("counter", counter)],
                   s.H_grind(pk_seed, s.WotsCGrind(height, index), digest, counter))

        for start, stop in [(0, 15), (3, 9), (5, 5)]:
            w.case("wots_c_chain_iter",
                   [("node", node), ("start", start), ("stop", stop), ("pk_seed", pk_seed)]
                   + anchor + [("chain_index", 9)],
                   s.wots_c_chain_iter(node, start, stop, pk_seed, height, index, 9))

        grinded = s.wots_c_grind_to_constant_sum(pk_seed, digest, height, index)
        assert grinded is not None
        counter, indexes = grinded
        w.case("wots_c_grind_to_constant_sum",
               [("pk_seed", pk_seed), ("message_digest", digest)] + anchor, grinded)
        w.case("wots_c_map_digest",
               [("pk_seed", pk_seed), ("message_digest", digest)] + anchor + [("counter", counter)],
               s.wots_c_map_digest(pk_seed, digest, height, index, counter))
        rejected = next(c for c in range(2**16)
                        if s.wots_c_map_digest(pk_seed, digest, height, index, c) is None)
        w.case("wots_c_map_digest",
               [("pk_seed", pk_seed), ("message_digest", digest)] + anchor + [("counter", rejected)],
               None)

        public_key = s.wots_c_pubkey_gen(sk_seed, pk_seed, height, index, balanced, depth)
        w.case("wots_c_pubkey_gen",
               [("sk_seed", sk_seed), ("pk_seed", pk_seed)] + anchor + shape, public_key)
        signature = s.wots_c_sign(digest, sk_seed, pk_seed, height, index, balanced, depth)
        assert signature is not None
        w.case("wots_c_sign",
               [("message_digest", digest), ("sk_seed", sk_seed), ("pk_seed", pk_seed)]
               + anchor + shape, signature)
        recovered = s.wots_c_pubkey_from_sig(signature, digest, pk_seed, height, index)
        assert recovered == public_key
        w.case("wots_c_pubkey_from_sig",
               [("signature", signature), ("message_digest", digest), ("pk_seed", pk_seed)]
               + anchor, recovered)
        bad = rejected.to_bytes(2) + signature[2:]
        assert s.wots_c_pubkey_from_sig(bad, digest, pk_seed, height, index) is None
        w.case("wots_c_pubkey_from_sig",
               [("signature", bad), ("message_digest", digest), ("pk_seed", pk_seed)] + anchor,
               None)

    return w


HEADER = f"""\
# WOTS+C reference vectors for libshrincs.
# Generated by test/spec/gen_vectors.py from shrincs-bip {REFERENCE}
# at commit {PINNED_COMMIT}.
#
# One case per block, blocks separated by a blank line. The first line names
# the function, the following lines give its arguments in the order of the
# Python signature, and the last line gives the result. An address argument
# is spelled as the fields of its class. Byte strings are hex, integers are
# decimal, a boolean is 0 or 1, a list is its elements separated by spaces,
# and a missing result is "none". A grinding result is the counter, a colon
# and the indexes.
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--shrincs-bip", default="../shrincs-bip",
                        help="path to a shrincs-bip checkout at the pinned commit")
    parser.add_argument("-o", "--out", required=True, help="output file")
    arguments = parser.parse_args()

    writer = generate(load_reference(Path(arguments.shrincs_bip)))
    Path(arguments.out).write_text(HEADER + "\n" + "\n".join(writer.lines))
    sys.stderr.write(f"wrote {arguments.out}: {writer.count} cases\n")


if __name__ == "__main__":
    main()
