#!/usr/bin/env python3
"""
Fix simpa → simp warnings in Kernel Clean.lean
"""

def fix_line(line, replacement):
    """Replace a specific pattern in line"""
    return replacement + '\n' if not line.endswith('\n') else replacement

fixes = {
    # Line 380: simpa using → simp at
    380: "    exact Nat.lt_irrefl 0 (by simp [h_size_zero] at hf)",
    # Line 384: simpa using → simp at then exact
    384: "    simp [h_list] at this; exact this",
    # Line 488: simpa using → simp at
    488: "    exact Nat.lt_irrefl 0 (by simp [h_size_zero] at hf)",
    # Line 492: simpa using → simp at then exact
    492: "    simp [h_list] at this; exact this",
    # Line 509: simpa → simp
    509: "    simp [h_rest_eq] using h_tail",
}

with open('Metamath/KernelClean.lean', 'r') as f:
    lines = f.readlines()

for line_num, new_text in fixes.items():
    idx = line_num - 1
    if idx < len(lines):
        lines[idx] = new_text if new_text.endswith('\n') else new_text + '\n'

with open('Metamath/KernelClean.lean', 'w') as f:
    f.writelines(lines)

print(f"✓ Fixed {len(fixes)} simpa warnings in KernelClean.lean")
