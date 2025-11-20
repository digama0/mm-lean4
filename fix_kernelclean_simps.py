#!/usr/bin/env python3
"""
Fix remaining unused simp arguments in KernelClean.lean

Based on warnings from lake build output.
"""

def fix_file(filepath, fixes):
    """
    Apply fixes: list of (line_num, args_to_remove: list[str])
    """
    with open(filepath, 'r') as f:
        lines = f.readlines()

    for line_num, args_to_remove in fixes:
        idx = line_num - 1
        if idx < len(lines):
            line = lines[idx]
            for arg in args_to_remove:
                # Remove the argument from simp calls
                # Handle patterns like: simp [arg1, arg2, arg3]
                # Try to match with comma before or after
                import re

                # Pattern 1: arg followed by comma (middle or start of list)
                line = re.sub(rf'\b{re.escape(arg)},\s*', '', line)
                # Pattern 2: comma followed by arg (end of list)
                line = re.sub(rf',\s*\b{re.escape(arg)}\b', '', line)
                # Pattern 3: only arg in brackets
                line = re.sub(rf'\[{re.escape(arg)}\]', '[]', line)
                # Pattern 4: arg with no comma (only item, or after removing others)
                line = re.sub(rf'\b{re.escape(arg)}\b', '', line)

            lines[idx] = line

    with open(filepath, 'w') as f:
        f.writelines(lines)

    print(f"✓ Fixed {len(fixes)} lines in {filepath}")


# KernelClean.lean fixes based on warnings
fix_file('Metamath/KernelClean.lean', [
    (1422, ['List.mapM_cons']),
    (1427, ['List.mapM_cons']),
    (1675, ['Array.getElem!_toList']),
    (1782, ['h_find']),
    (1787, ['h_find']),
    (1790, ['h_find']),
    (1794, ['h_find']),
    (1799, ['h_expr']),
    (1820, ['h_find']),
    (1823, ['h_find']),
    (1986, ['Array.toList_extract_dropLastN stack k h']),
    (1995, ['Array.window_toList_map stack off len toExpr h']),
    (2487, ['List.flatMap_cons']),
    (2503, ['Spec.Variable.mk']),
    (2506, ['List.map_append', 'List.map']),
    (2748, ['h0']),
    (2759, ['h0']),
    (2936, ['ite_false']),
    (2965, ['getElem!_pos']),
    (3000, ['getElem!_pos']),
    (3037, ['getElem!_pos']),
    (3064, ['getElem!_pos']),
    (3103, ['getElem!_pos']),
    (3136, ['getElem!_pos']),
    (3731, ['Bind.bind', 'Except.bind']),
    (3738, ['Functor.map', 'Except.map']),
])

print("\n✓ All KernelClean.lean unused simp arguments fixed!")
