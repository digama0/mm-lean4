#!/usr/bin/env python3
"""
Fix unused variable warnings
"""
import re

def fix_unused_var(line, var_name):
    """Replace variable name with underscore"""
    # Try to replace the variable binding
    # Pattern: (var_name : Type) -> (_ : Type)
    # Pattern: (var_name) -> (_)
    # Pattern: var_name => -> _ =>

    # For function parameters with types
    line = re.sub(rf'\b{re.escape(var_name)}\s*:', r'_:', line)
    # For lambda parameters
    line = re.sub(rf'\b{re.escape(var_name)}\s*=>', r'_ =>', line)
    return line

with open('Metamath/KernelClean.lean', 'r') as f:
    lines = f.readlines()

# Based on warnings output
fixes = [
    (1983, 'h'),  # unused variable `h`
    (1990, 'h'),  # unused variable `h`
    (2698, 'h_bound'),
    (2700, 'h_sz'),
    (2771, 'lbl'),
    (2872, 'lbl\''),
    (3452, 'h_i'),
    (3468, 'db'),
    (3468, 'dv'),
    (3469, 'σ_impl'),
    (3470, 'σ_typed'),
    (3613, 'needed'),
]

for line_num, var_name in fixes:
    idx = line_num - 1
    if idx < len(lines):
        lines[idx] = fix_unused_var(lines[idx], var_name)

with open('Metamath/KernelClean.lean', 'w') as f:
    f.writelines(lines)

print(f"✓ Fixed {len(fixes)} unused variable warnings in KernelClean.lean")

# Fix DBCaseAnalysis
with open('Metamath/DBCaseAnalysis.lean', 'r') as f:
    lines = f.readlines()

# Line 129: unused variable `pos`
idx = 129 - 1
if idx < len(lines):
    lines[idx] = fix_unused_var(lines[idx], 'pos')

with open('Metamath/DBCaseAnalysis.lean', 'w') as f:
    f.writelines(lines)

print(f"✓ Fixed 1 unused variable warning in DBCaseAnalysis.lean")
