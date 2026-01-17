#!/usr/bin/env python3
"""
Extract theorem/def/structure signatures from Lean files.
Outputs markdown with signatures only (no proof bodies).
"""
import re
import sys
from pathlib import Path

DECL_RE = re.compile(r'^(def|theorem|lemma|structure|class|instance|axiom|abbrev)\b')

def extract_signatures(text: str, filename: str) -> list[str]:
    lines = text.splitlines()
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        if DECL_RE.match(line.lstrip()):
            buf = [line]
            i += 1
            # Collect until we hit ':= by' or ':=' starting a proof/body
            while i < len(lines):
                l = lines[i]
                stripped = l.strip()

                # Stop conditions - proof body starting
                if ':= by' in l or l.rstrip().endswith(':= by'):
                    # Include the line but truncate at ':= by'
                    parts = l.split(':= by')
                    buf.append(parts[0].rstrip() + ' := by ...')
                    break
                if re.search(r':=\s*$', l):
                    buf.append(l.rstrip() + ' ...')
                    break
                if stripped.startswith('where'):
                    buf.append(l)
                    # For structures, capture field names but not defaults
                    i += 1
                    while i < len(lines) and (lines[i].startswith('  ') or lines[i].strip() == ''):
                        field_line = lines[i]
                        # Keep field declarations but truncate any := defaults
                        if ':=' in field_line and not field_line.strip().startswith('--'):
                            field_line = field_line.split(':=')[0].rstrip()
                        if field_line.strip() and not field_line.strip().startswith('--'):
                            buf.append(field_line)
                        i += 1
                    break
                # Stop on unindented line (new declaration)
                if stripped and not l.startswith(' ') and not l.startswith('\t'):
                    break
                # Stop on blank line followed by unindented content
                if stripped == '' and i + 1 < len(lines):
                    next_line = lines[i + 1]
                    if next_line and not next_line.startswith(' '):
                        break
                buf.append(l)
                i += 1

            sig = '\n'.join(buf).rstrip()
            if sig:
                out.append(sig)
        else:
            i += 1
    return out

def main(root: str):
    rootp = Path(root)
    files = sorted(rootp.rglob("*.lean"))

    print("# Audit Signatures - Riemann Project")
    print()
    print("All definitions, theorems, structures, and classes.")
    print("Proof bodies omitted for reviewability.")
    print()
    print("---")
    print()

    total_sigs = 0
    for f in files:
        # Skip .lake directory
        if '.lake' in str(f):
            continue
        try:
            txt = f.read_text(encoding="utf-8", errors="ignore")
        except:
            continue
        sigs = extract_signatures(txt, str(f))
        if not sigs:
            continue

        rel_path = f.relative_to(rootp)
        print(f"## {rel_path}")
        print()
        for s in sigs:
            print("```lean")
            print(s)
            print("```")
            print()
            total_sigs += 1

    print("---")
    print()
    print(f"**Total signatures extracted: {total_sigs}**")

if __name__ == "__main__":
    root = sys.argv[1] if len(sys.argv) > 1 else "."
    main(root)
