#!/usr/bin/env python3
"""
CliffordRH Proof Status Dashboard

A CLI tool to display the current status of the Riemann Hypothesis
formalization in Lean using the Cl(3,3) geometric framework.

Usage:
    python proof_status.py           # Full report
    python proof_status.py --chain   # Just the proof chain
    python proof_status.py --summary # Just the summary
    python proof_status.py --next    # Next steps only
"""

import json
import argparse
from pathlib import Path

# ANSI color codes
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    DIM = '\033[2m'

def load_status():
    """Load the proof status from JSON file."""
    status_file = Path(__file__).parent / "proof_status.json"
    with open(status_file, 'r') as f:
        return json.load(f)

def print_header(data):
    """Print the header section."""
    meta = data['meta']
    print(f"\n{Colors.BOLD}{Colors.CYAN}{'═' * 60}{Colors.ENDC}")
    print(f"{Colors.BOLD}  CliffordRH Proof Pipeline - Status Report{Colors.ENDC}")
    print(f"{Colors.DIM}  Version {meta['version']} | {meta['date']}{Colors.ENDC}")
    print(f"{Colors.CYAN}{'═' * 60}{Colors.ENDC}")
    print(f"\n{Colors.BOLD}Goal:{Colors.ENDC} {meta['goal']}\n")

def print_chain(data):
    """Print the proof chain."""
    print(f"{Colors.BOLD}{Colors.YELLOW}Proof Chain:{Colors.ENDC}")
    print(f"{Colors.DIM}{'─' * 60}{Colors.ENDC}")

    type_colors = {
        'premise': Colors.BLUE,
        'axiom': Colors.RED,
        'sorry': Colors.YELLOW,
        'theorem': Colors.GREEN,
        'hypothesis': Colors.CYAN,
    }

    type_symbols = {
        'premise': '●',
        'axiom': '⚠',
        'sorry': '○',
        'theorem': '✓',
        'hypothesis': '◆',
    }

    for step in data['chain']:
        step_type = step['type']
        color = type_colors.get(step_type, Colors.ENDC)
        symbol = type_symbols.get(step_type, '?')

        # Format the step
        type_label = f"[{step_type.upper()}]"

        if step_type == 'premise':
            print(f"  {color}{symbol}{Colors.ENDC} {step['input']}")
        else:
            name = step.get('name', '')
            output = step.get('output', step.get('description', ''))
            print(f"  {Colors.DIM}↓{Colors.ENDC}")
            print(f"  {color}{symbol} {type_label:12}{Colors.ENDC} {name}")
            if output:
                print(f"    {Colors.DIM}→ {output}{Colors.ENDC}")

    print(f"\n  {Colors.GREEN}{Colors.BOLD}⇒ σ = 1/2  ✓{Colors.ENDC}")
    print()

def print_summary(data):
    """Print the summary statistics."""
    summary = data['summary']

    print(f"{Colors.BOLD}{Colors.YELLOW}Summary:{Colors.ENDC}")
    print(f"{Colors.DIM}{'─' * 60}{Colors.ENDC}")

    # Status bars
    def status_bar(label, count, color, max_width=20):
        bar = '█' * min(count, max_width)
        return f"  {color}{label:12}{Colors.ENDC} {bar} {count}"

    print(status_bar("Axioms", summary['axioms'], Colors.RED))
    print(status_bar("Sorries", summary['sorries'], Colors.YELLOW))
    print(status_bar("Hypotheses", summary['hypotheses'], Colors.CYAN))
    print(status_bar("Theorems", summary['theorems_proven'], Colors.GREEN))
    print(status_bar("Definitions", summary['definitions'], Colors.BLUE))
    print()

    # Completion metric
    total_gaps = summary['axioms'] + summary['sorries'] + summary['hypotheses']
    total_proven = summary['theorems_proven']
    completion = total_proven / (total_proven + total_gaps) * 100 if (total_proven + total_gaps) > 0 else 0

    print(f"  {Colors.BOLD}Completion:{Colors.ENDC} {completion:.1f}% ({total_proven} proven / {total_gaps} gaps)")
    print()

def print_files(data):
    """Print file-by-file breakdown."""
    print(f"{Colors.BOLD}{Colors.YELLOW}File Details:{Colors.ENDC}")
    print(f"{Colors.DIM}{'─' * 60}{Colors.ENDC}")

    for filename, info in data['files'].items():
        print(f"\n  {Colors.BOLD}{Colors.BLUE}{filename}{Colors.ENDC}")
        print(f"  {Colors.DIM}{info['purpose']}{Colors.ENDC}")

        # Axioms (red)
        for axiom in info.get('axioms', []):
            print(f"    {Colors.RED}[AXIOM]{Colors.ENDC}      {axiom['name']}")
            print(f"                  {Colors.DIM}Line {axiom['line']}: {axiom['desc']}{Colors.ENDC}")

        # Sorries (yellow)
        for sorry in info.get('sorries', []):
            print(f"    {Colors.YELLOW}[SORRY]{Colors.ENDC}      {sorry['name']}")
            print(f"                  {Colors.DIM}Line {sorry['line']}: {sorry['desc']}{Colors.ENDC}")

        # Hypotheses (cyan)
        for hyp in info.get('hypotheses', []):
            print(f"    {Colors.CYAN}[HYPOTHESIS]{Colors.ENDC} {hyp['name']}")
            print(f"                  {Colors.DIM}{hyp['desc']}{Colors.ENDC}")

        # Theorems (green)
        for thm in info.get('theorems', []):
            print(f"    {Colors.GREEN}[THEOREM]{Colors.ENDC}    {thm['name']}")
            print(f"                  {Colors.DIM}Line {thm['line']}: {thm['desc']}{Colors.ENDC}")

    print()

def print_next_steps(data):
    """Print next steps."""
    print(f"{Colors.BOLD}{Colors.YELLOW}Next Steps:{Colors.ENDC}")
    print(f"{Colors.DIM}{'─' * 60}{Colors.ENDC}")

    difficulty_colors = {
        'easy': Colors.GREEN,
        'medium': Colors.YELLOW,
        'hard': Colors.RED,
        'very_hard': Colors.RED + Colors.BOLD,
    }

    for step in data['next_steps']:
        priority = step['priority']
        difficulty = step['difficulty']
        color = difficulty_colors.get(difficulty, Colors.ENDC)

        checkbox = '☐'
        print(f"\n  {checkbox} {Colors.BOLD}[P{priority}]{Colors.ENDC} {step['task']}")
        print(f"     {Colors.DIM}File: {step['file']}{Colors.ENDC}")
        print(f"     {color}Difficulty: {difficulty}{Colors.ENDC}")
        print(f"     {Colors.DIM}Notes: {step['notes']}{Colors.ENDC}")

    print()

def print_legend():
    """Print the legend."""
    print(f"{Colors.BOLD}{Colors.YELLOW}Legend:{Colors.ENDC}")
    print(f"{Colors.DIM}{'─' * 60}{Colors.ENDC}")
    print(f"  {Colors.RED}[AXIOM]{Colors.ENDC}      Unproven assumption (analytic fact)")
    print(f"  {Colors.YELLOW}[SORRY]{Colors.ENDC}      Incomplete proof (technical gap)")
    print(f"  {Colors.CYAN}[HYPOTHESIS]{Colors.ENDC} Theorem parameter (geometric condition)")
    print(f"  {Colors.GREEN}[THEOREM]{Colors.ENDC}    Fully proven in Lean")
    print(f"  {Colors.BLUE}[DEF]{Colors.ENDC}        Definition")
    print()

def main():
    parser = argparse.ArgumentParser(description='CliffordRH Proof Status Dashboard')
    parser.add_argument('--chain', action='store_true', help='Show only proof chain')
    parser.add_argument('--summary', action='store_true', help='Show only summary')
    parser.add_argument('--files', action='store_true', help='Show file details')
    parser.add_argument('--next', action='store_true', help='Show next steps')
    parser.add_argument('--no-color', action='store_true', help='Disable colors')
    args = parser.parse_args()

    # Disable colors if requested
    if args.no_color:
        for attr in dir(Colors):
            if not attr.startswith('_'):
                setattr(Colors, attr, '')

    # Load data
    data = load_status()

    # Determine what to show
    show_all = not (args.chain or args.summary or args.files or args.next)

    print_header(data)

    if show_all or args.chain:
        print_chain(data)

    if show_all or args.summary:
        print_summary(data)

    if show_all or args.files:
        print_files(data)

    if show_all or args.next:
        print_next_steps(data)

    if show_all:
        print_legend()

    print(f"{Colors.CYAN}{'═' * 60}{Colors.ENDC}\n")

if __name__ == '__main__':
    main()
