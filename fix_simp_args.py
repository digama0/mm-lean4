#!/usr/bin/env python3
import re

def remove_simp_arg(line, arg_to_remove):
    """Remove a specific argument from a simp call."""
    # Match simp [args] or simp only [args]
    pattern = r'(simp(?:\s+only)?\s*\[)([^\]]+)(\])'
    match = re.search(pattern, line)
    if not match:
        return line
    
    prefix, args, suffix = match.groups()
    # Split arguments, remove the target, rejoin
    arg_list = [a.strip() for a in args.split(',')]
    arg_list = [a for a in arg_list if arg_to_remove not in a]
    
    if not arg_list:
        # If no args left, just use simp without brackets
        return re.sub(pattern, 'simp', line)
    
    new_args = ', '.join(arg_list)
    return re.sub(pattern, f'{prefix}{new_args}{suffix}', line)

def fix_file(filepath, fixes):
    """Apply fixes: list of (line_num, arg_to_remove)"""
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    for line_num, arg in fixes:
        idx = line_num - 1
        if idx < len(lines):
            lines[idx] = remove_simp_arg(lines[idx], arg)
    
    with open(filepath, 'w') as f:
        f.writelines(lines)
    print(f"✓ Fixed {len(fixes)} simp warnings in {filepath}")

# KernelClean.lean
fix_file('Metamath/KernelClean.lean', [
    (513, 'Array.toList'),
    (550, 'Array.toList_length'),
    (724, 'List.filterMap'),
    (728, 'List.filterMap'),
    (1259, 'toExprOpt'),
    (1414, 'hy'),
    (1422, 'List.mapM_cons'),
    (1422, 'h_fa'),
    (1427, 'List.mapM_cons'),
    (1427, 'h_fa'),
    (1431, 'hm'),
    (1523, 'getElem!_pos'),
    (1723, 'Array.getElem!_toList'),
    (1830, 'h_find'),
    (1835, 'h_find'),
    (1838, 'h_find'),
    (1842, 'h_find'),
    (1847, 'h_expr'),
    (1868, 'h_find'),
    (1871, 'h_find'),
    (2045, 'Array.toList_extract_dropLastN stack k h'),
    (2054, 'Array.window_toList_map stack off len toExpr h'),
    (2560, 'List.flatMap_cons'),
    (2576, 'Spec.Variable.mk'),
    (2579, 'List.map_append'),
    (2579, 'List.map'),
    (2821, 'h0'),
    (2832, 'h0'),
    (3009, 'ite_false'),
    (3038, 'getElem!_pos'),
    (3073, 'getElem!_pos'),
    (3110, 'getElem!_pos'),
    (3137, 'getElem!_pos'),
    (3176, 'getElem!_pos'),
    (3209, 'getElem!_pos'),
    (3859, 'Bind.bind'),
    (3859, 'Except.bind'),
    (3866, 'Functor.map'),
    (3866, 'Except.map'),
])

print("Done!")
