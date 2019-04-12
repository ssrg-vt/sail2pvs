#! /usr/bin/env python3

# -*- coding: utf-8 -*-
from . import util
from typing import List, Dict, Tuple


# Currify the return type
# input: [a->[b->c]]
# output: a -> b -> c
def parse_return_type(arg : str)->str:
    result = arg
    if '->' in arg and arg.startswith('[') and arg.endswith(']'):
        block = arg.strip().split('[', 1)[1].rsplit(']', 1)[0].strip()
        args = util.split_sep(block, '->')
        if len(args) == 1:
            result = '[' + block + ']'
        elif len(args) == 2:
            result = args[0].strip() + '->' + parse_return_type(args[1].strip())
    return result


def process_line(var_dict: Dict[str, str], fun_def: str)->Tuple[str, List[Tuple[str, str]]]:
    func_decl = util.split_sep_bks(fun_def, ':')
    func_name = func_decl[0].split('[', 1)[0].split('(', 1)[0]
    return_type = func_decl[1].split('=', 1)[0].strip()
    return_type = util.split_sep(return_type, ' ')[-1]
    return_type = parse_return_type(return_type)
    args = util.extract_bk_content(func_decl[0])
    arg_list = list(map(lambda arg:
                        util.parse_args(var_dict, arg.split('(', 1)[1].rsplit(')', 1)[0].strip()), args))
    arg_list.append(('', return_type))
    return func_name, arg_list


def process_function(var_dict: Dict[str, str], lines: str)->Tuple[str, List[Tuple[str, str]], str, str]:
    lines_split = util.split_sep_bks(lines, '=')
    fun_def = lines_split[0].replace('\n', ' ')
    fun_content = '='.join(lines_split[1:])
    func_name, arg_list = process_line(var_dict, fun_def)
    return func_name, arg_list, fun_def, fun_content


if __name__ == '__main__':
    func_name, arg_list, fun_def, fun_content = process_function({}, '''splitWhile_tr[A : TYPE](p : [A -> bool])(l : list[A])(acc : list[A]) : RECURSIVE [list[A], list[A]] = 
CASES l OF(
      null: (rev(acc), null[A]),
      cons(x, xs): IF p(x) THEN splitWhile_tr(p)(xs)(list_cons(x)(acc)) ELSE (rev(acc), list_cons(x)(xs)) ENDIF 
ENDCASES
MEASURE length(l)
''')
    print(arg_list)
    # arg_list == [('p', '[A -> bool]'), ('l', 'list[A]'), ('acc', 'list[A]'), ('', '[list[A], list[A]]')]