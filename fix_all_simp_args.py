#!/usr/bin/env python3
import re

def remove_simp_arg(line, arg_to_remove):
    """Remove a specific argument from a simp call."""
    # Handle different simp formats
    patterns = [
        (r'(simp(?:\s+only)?\s*\[)([^\]]+)(\])', 1, 2, 3),  # simp [args]
        (r'(simp\s+)(\[)([^\]]+)(\])', 1, 3, 4),  # simp [args] with space
    ]
    
    for pattern, *groups in patterns:
        match = re.search(pattern, line)
        if match:
            parts = match.groups()
            prefix = ''.join(parts[:groups[0]])
            args = parts[groups[1]]
            suffix = ''.join(parts[groups[2]:]) if len(parts) > groups[2] else ''
            
            # Split arguments, remove the target
            arg_list = [a.strip() for a in args.split(',')]
            # Remove args that contain the target string
            arg_list = [a for a in arg_list if arg_to_remove not in a]
            
            if not arg_list:
                # If no args left, just use simp
                return re.sub(pattern, 'simp', line)
            
            new_args = ', '.join(arg_list)
            bracket_start = match.group(groups[1]) if len(groups) > 1 else '['
            bracket_end = ']'
            return re.sub(pattern, f'{prefix}{bracket_start}{new_args}{bracket_end}', line)
    
    return line

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

# DBCaseAnalysis.lean - Fix remaining unused simp args
fix_file('Metamath/DBCaseAnalysis.lean', [
    (91, 'if_pos h\''),
    (263, 'h_obj'),
    (287, 'h_obj'),
    (302, 'h_obj'),
    (313, 'h_obj'),
    (323, 'h_obj'),
    (334, 'h_obj'),
    (344, 'h_obj'),
    (355, 'h_obj'),
    (735, 'ite_false'),
    (967, 'ite_false'),
    (1139, 'h_float_cond'),
    (1139, 'h_f1'),
    (1143, 'h_float_cond'),
    (1143, 'h_f1'),
    (1155, 'Bool.and_eq_true'),
    (1157, 'h_float_cond'),
    (1157, 'h_f1'),
    (1164, 'h_float_cond'),
    (1164, 'h_f1'),
    (1168, 'h_float_cond'),
    (1168, 'h_f1'),
    (1174, 'decide_eq_true_eq'),
    (1179, 'h_float_cond'),
    (1179, 'h_dup'),
    (1183, 'h_float_cond'),
    (1183, 'h_dup'),
])

# KernelClean.lean - Fix remaining unused simp args
fix_file('Metamath/KernelClean.lean', [
    (118, 'getElem!_def'),
    (168, 'h_init'),
    (177, 'Array.toList_push'),
    (177, 'ih'),
    (177, 'List.append_assoc'),
    (188, 'h_init'),
    (267, 'Except.bind'),
    (270, 'h_init'),
    (319, 'Except.bind'),
    (322, 'h_init'),
])

print("\n✓ All unused simp arguments fixed!")
