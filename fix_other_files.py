#!/usr/bin/env python3
import re

def remove_simp_arg(line, arg_to_remove):
    """Remove a specific argument from a simp call."""
    pattern = r'(simp(?:\s+only)?\s*\[)([^\]]+)(\])'
    match = re.search(pattern, line)
    if not match:
        return line
    
    prefix, args, suffix = match.groups()
    arg_list = [a.strip() for a in args.split(',')]
    arg_list = [a for a in arg_list if arg_to_remove not in a]
    
    if not arg_list:
        return re.sub(pattern, 'simp', line)
    
    new_args = ', '.join(arg_list)
    return re.sub(pattern, f'{prefix}{new_args}{suffix}', line)

def fix_file(filepath, fixes):
    with open(filepath, 'r') as f:
        lines = f.readlines()
    
    for line_num, arg in fixes:
        idx = line_num - 1
        if idx < len(lines):
            lines[idx] = remove_simp_arg(lines[idx], arg)
    
    with open(filepath, 'w') as f:
        f.writelines(lines)
    print(f"✓ Fixed {len(fixes)} simp warnings in {filepath}")

# DBCaseAnalysis.lean
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

# CounterexampleInsertError.lean
fix_file('Metamath/CounterexampleInsertError.lean', [
    (57, 'if_pos'),
])

# ParserProofs.lean
fix_file('Metamath/ParserProofs.lean', [
    (142, 'h_some'),
    (142, 'h'),
    (144, 'h'),
    (164, 'DB.mkError_frame'),
    (233, 'DB.find?'),
    (233, 'hok'),
    (278, 'DB.find?'),
    (278, 'hok'),
    (325, 'ite_false'),
    (381, 'DB.insert'),
    (381, 'DB.find?'),
    (399, 'hfind'),
    (412, 'hok'),
    (426, 'hfind'),
    (437, 'hfind'),
    (437, 'hobj'),
    (437, 'hok'),
    (447, 'hok'),
    (457, 'hok'),
    (467, 'hok'),
    (480, 'hfind'),
    (490, 'hok'),
    (502, 'hfind'),
    (511, 'hok'),
    (696, 'ite_true'),
    (986, 'Array.extract'),
    (993, 'Array.extract'),
    (1064, 'Std.HashMap.empty'),
    (1106, 'DB.error_mkError'),
    (1234, 'hfind_old'),
    (1268, 'DB.error_mkError'),
])

print("Done!")
