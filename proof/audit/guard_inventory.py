# SPDX-License-Identifier: MIT
#
# libshrincs - formally verified SHRINCS implementations.
#

"""Check guard coverage and full-type pins in the compiled proof directory."""

from pathlib import Path
import re
import subprocess
import sys


def commands(source):
    result = subprocess.run(
        ['awk', '-v', 'emit_commands=1', '-f',
         str(Path(__file__).with_name('declarations.awk')), str(source)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise SystemExit(result.stderr.rstrip())
    for line in result.stdout.splitlines():
        yield line.split('\t', 2)


def library(source):
    return '.'.join(('Shrincs', *source.with_suffix('').parts))


def declarations(source, kinds):
    for modules, _sections, command in commands(source):
        match = re.match(rf'(?:HB\.instance\s+)?(?:{kinds})\s+([\w\']+)', command)
        if match and match[1] != '_':
            yield '.'.join(part for part in (library(source), modules, match[1]) if part)


def compile_query(source, output, flags):
    result = subprocess.run(['coqc', *flags, str(source)], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output.write_text(result.stdout)
    if result.returncode:
        print('\n'.join(line for line in result.stdout.splitlines()
                        if not line.startswith('Fetching opaque proofs from disk')),
              file=sys.stderr)
        raise SystemExit(f'{source} does not compile')
    return result.stdout


def main():
    guards, output = map(Path, sys.argv[1:3])
    flags = sys.argv[3:]
    if not guards.is_file():
        raise SystemExit(f'{guards} missing')
    checks = {}
    for _modules, _sections, command in commands(guards):
        match = re.fullmatch(r'Check\s+\(@?(Shrincs\.internal\.ssprove\.'
                             r'(?:lib|fxmss|wots)\.guard\.[\w.\']+)\s*:\s*(.+)\)',
                             command)
        if match:
            checks[match[1]] = match[2]

    sources = [Path('games.v'), Path('schemes.v')] + sorted(
        p for p in Path('internal/ssprove').rglob('*.v') if 'guard' not in p.parts)
    inventory = [Path(__file__).with_suffix('.v.in').read_text()]
    for source in sources:
        if not source.with_suffix('.vo').is_file():
            raise SystemExit(f'{source}: inventory needs a built .vo (Dune owns freshness)')
        inventory.append(f'Require {library(source)}.\n')
        for name in declarations(source, 'Definition|Fixpoint|CoFixpoint'):
            inventory.append(f'Goal True. let t := type of @{name} in '
                             f'guard_find_game ltac:(idtac "GUARD_GAME {name}") t. '
                             'exact I. Qed.\n')
    probe = output / 'guard_inventory.v'
    probe.write_text(''.join(inventory))
    result = compile_query(probe, output / 'guard_inventory.out', flags)
    games = re.findall(r'^GUARD_GAME (\S+)$', result, re.M)
    errors = []
    for name in games:
        if not any(re.search(r'\bAdvOf\b', typ) and
                   re.search(r'(?<![\w.\'])' + re.escape(name) + r'(?![\w.\'])', typ)
                   for typ in checks.values()):
            errors.append(f'{name} has no pinned guard')
    for source in sorted(p for p in Path('internal/ssprove').rglob('*.v')
                         if 'guard' in p.parts):
        for name in declarations(source, 'Lemma|Theorem|Corollary|Fact|Remark|Proposition'):
            if name not in checks:
                errors.append(f'{name} has no full-type Check')
    if errors:
        raise SystemExit('\n'.join(errors))
    if not games or not checks:
        raise SystemExit('empty guard inventory')
    compile_query(guards, output / 'guards.out', flags)
    print(f'guard coverage: {len(games)} games, {len(checks)} pinned guards')


if __name__ == '__main__':
    main()
