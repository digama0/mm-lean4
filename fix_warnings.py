#!/usr/bin/env python3
"""
Systematically fix linter warnings across the codebase.
"""

import re
from pathlib import Path

def fix_file(filepath, fixes):
    """Apply list of (line_num, pattern, replacement) tuples to a file."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    for line_num, pattern, replacement in fixes:
        idx = line_num - 1
        if idx < len(lines):
            lines[idx] = lines[idx].replace(pattern, replacement)

    with open(filepath, 'w') as f:
        f.writelines(lines)

    print(f"✓ Fixed {len(fixes)} warnings in {filepath}")

# Fix unused variables by replacing with _
def fix_unused_var(filepath, line_num, var_name):
    with open(filepath, 'r') as f:
        lines = f.readlines()

    idx = line_num - 1
    if idx < len(lines):
        # Replace the variable name with underscore, preserving the pattern
        lines[idx] = re.sub(r'\b' + re.escape(var_name) + r'\b', '_', lines[idx], count=1)

    with open(filepath, 'w') as f:
        f.writelines(lines)

# Fix simpa → simp
def fix_simpa(filepath, line_num):
    with open(filepath, 'r') as f:
        lines = f.readlines()

    idx = line_num - 1
    if idx < len(lines) and 'simpa' in lines[idx]:
        lines[idx] = lines[idx].replace('simpa', 'simp')

    with open(filepath, 'w') as f:
        f.writelines(lines)

# Main fixes
print("Fixing linter warnings...")

# KernelClean.lean - Change 'simpa using' to 'simp at'
fix_file('Metamath/KernelClean.lean', [
    (230, 'simpa using h_nonempty', 'simp at h_nonempty'),
    (235, 'simpa', 'simp'),
    (380, 'simpa using hf', 'simp at hf'),
    (384, 'simpa', 'simp'),
    (488, 'simpa using hf', 'simp at hf'),
    (492, 'simpa', 'simp'),
    (509, 'simpa', 'simp'),
    (1486, 'simpa', 'simp'),
])

# Fix unused variables in KernelClean
fix_unused_var('Metamath/KernelClean.lean', 2042, 'h')
fix_unused_var('Metamath/KernelClean.lean', 2049, 'h')
fix_unused_var('Metamath/KernelClean.lean', 2771, 'h_bound')
fix_unused_var('Metamath/KernelClean.lean', 2773, 'h_sz')
fix_unused_var('Metamath/KernelClean.lean', 2844, 'lbl')
fix_unused_var('Metamath/KernelClean.lean', 2945, 'lbl\'')
fix_unused_var('Metamath/KernelClean.lean', 3525, 'h_i')
fix_unused_var('Metamath/KernelClean.lean', 3541, 'db')
fix_unused_var('Metamath/KernelClean.lean', 3541, 'dv')  # Same line, second var
fix_unused_var('Metamath/KernelClean.lean', 3542, 'σ_impl')
fix_unused_var('Metamath/KernelClean.lean', 3543, 'σ_typed')
fix_unused_var('Metamath/KernelClean.lean', 3735, 'needed')

# ArrayListExt.lean
fix_simpa('Metamath/ArrayListExt.lean', 378)
fix_simpa('Metamath/ArrayListExt.lean', 382)
fix_simpa('Metamath/ArrayListExt.lean', 433)
fix_unused_var('Metamath/ArrayListExt.lean', 679, 'h')
fix_unused_var('Metamath/ArrayListExt.lean', 781, 'h')
fix_unused_var('Metamath/ArrayListExt.lean', 807, 'h')

# Bridge/Basics.lean
fix_unused_var('Metamath/Bridge/Basics.lean', 105, 'c')
fix_unused_var('Metamath/Bridge/Basics.lean', 217, 'c')
fix_unused_var('Metamath/Bridge/Basics.lean', 217, 'v')  # Same line

# ParserInvariants.lean
fix_unused_var('Metamath/ParserInvariants.lean', 445, 'h_ne')
fix_unused_var('Metamath/ParserInvariants.lean', 652, 'h_success')

# ParserCorrectness.lean
fix_unused_var('Metamath/ParserCorrectness.lean', 485, 'h')

# DBCaseAnalysis.lean
fix_unused_var('Metamath/DBCaseAnalysis.lean', 129, 'pos')
fix_unused_var('Metamath/DBCaseAnalysis.lean', 613, 'pos')
fix_unused_var('Metamath/DBCaseAnalysis.lean', 1285, 'db')

# ParserProofs.lean
fix_unused_var('Metamath/ParserProofs.lean', 1390, 'h_ne')

print("\n✓ All unused variable warnings fixed!")
