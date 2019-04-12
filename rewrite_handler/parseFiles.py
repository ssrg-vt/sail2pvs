#! /usr/bin/env python3

# -*- coding: utf-8 -*-
import os
import re
import copy
from . import util
from . import parseDatatype
from . import parseFunction
from typing import List, Tuple

S_STATE, S_DATATYPE = range(2)

function_dict = {}
type_dict = {}
type_dict['list'] = (['T'], {'cons': '[T,list[T]]', 'null': ''})

file_dict = {}


def gen_deps(dep_dict):
    mod_list = list(dep_dict.keys())
    mod_num = len(mod_list)
    module_list = []
    while len(module_list) < mod_num:
        for mod in mod_list:
            dep_list = list(dep_dict[mod])
            if not dep_list and mod not in module_list:
                module_list.append(mod)
            dep_dict[mod] = util.diff_list(dep_list, module_list)
    return module_list


def gen_dep_for_src_files(module_dict, src_data, lib_name):
    modules = list(module_dict.keys())
    new_mod_dict = copy.deepcopy(module_dict)
    file_list = []
    dep_dict = {}
    for module in modules:
        dep_dict[module] = []
        src = src_data[module]
        modules = re.findall(util.importPat, src)
        for line in modules:
            module_name = line.strip()
            if module_name in list(new_mod_dict.keys()):
                dep_dict[module].append(module_name)
    module_list = gen_deps(dep_dict)
    for mod in module_list:
        file_list.append(new_mod_dict[mod])
    file_dict[lib_name] = file_list


# Check whether the library path is valid
# If so, generate dependency relations between different files under the library
def gen_lib_deps(lib_path: str):
    lib_name = lib_path.split('/')[-1]
    if not os.path.isdir(lib_path):
        print('There does not exist such library named ' + lib_name)
        return
    src_data = {}
    module_dict = {}
    files = [f for f in os.listdir(lib_path) if f.endswith('.pvs') and not f.endswith('_adt.pvs')]
    for file_name in files:
        theory_name = file_name.split('.')[0]
        module_dict[theory_name] = file_name
        with open(os.path.join(lib_path, file_name)) as f:
            src_data[theory_name] = f.read()
    gen_dep_for_src_files(module_dict, src_data, lib_name)


def parse_file(file_path):
    updated_content = ''
    with open(file_path) as f:
        lines = f.readlines()
        var_dict = {}
        type_dec = []
        state = S_STATE
        for line in lines:
            if line.startswith('%') or 'LEMMA' in line:
                pass
            elif state == S_STATE:
                if util.varPat.search(line.replace(' ', '')):
                    updated_content += line
                    decs = line.split(':')
                    variables = decs[0].replace(' ', '').split(',')
                    util.logger.debug('declarations:')
                    util.logger.debug(line)
                    vtype = decs[1].split("VAR")[1]
                    for v in variables:
                        var_dict[v] = vtype.replace(' ', '')
                elif 'DATATYPE' in line:
                    updated_content += line
                    type_dec.clear()
                    type_dec.append(line)
                    state = S_DATATYPE
                elif ':TYPE=' in line.replace(' ', '') or ':TYPE+=' in line.replace(' ', '') or ':TYPE\n' in line.replace(' ', '') or (': THEORY' in line and ']' in line) or (util.constPat.search(line) and '->' not in line and 'THEORY' not in line and 'LAMBDA' not in line and not line.endswith(',\n') and '(#' not in line):
                    pass
                elif (util.pvsDefPat.search(line) or util.constPat.search(line)) and ':' in line and '=' in line:
                    func_name, arg_list = parseFunction.process_line(var_dict, line)
                    function_dict[func_name] = arg_list
            elif state == S_DATATYPE:
                to_continue = True
                if 'END ' in line:
                    name, (tvs, contents) = parseDatatype.parse_datatype(var_dict, type_dec)
                    type_dict[name] = (tvs, contents)
                    state = S_STATE
                    to_continue = False
                if to_continue:
                    type_dec.append(line)


def infer_exp_type(exp, arg_list):
    exp = exp.strip()
    for arg in arg_list:
        # If the expression is already in the argument type list
        if exp == arg[util.u_name]:
            return arg[util.u_annotation]
    if util.functionAppPat.search(exp):
        func_name = exp.split('(')[0].split('[')[0]
        if func_name in function_dict.keys():
            func_arg_list = function_dict[func_name]
            ret_type = func_arg_list[-1][1]
            return ret_type
    elif exp.startswith('(') and exp.endswith(')'):
        return '[' + exp.split('(', 1)[1].rsplit(')', 1)[0].strip() + ']'
    return None


# Simple type inference
# exp: the expression that requires type information
# arg_list: current mapping from variables to their types
# output: type (tuple, function, datatype, or other), the annotation of type, datatype name (if it is a datatype)
def exp_type_string(exp, arg_list):
    exp_type = infer_exp_type(exp, arg_list)
    if not exp_type:
        return None, None, None
    exp_type_split = util.split_sep_bks(exp_type, '->')
    if len(exp_type_split) > 1:
        return util.t_function, exp_type, None
    elif exp_type.startswith('['):
        return util.t_tuple, exp_type, None
    else:
        e_name = exp_type.split('[')[0].strip()
        if e_name in type_dict.keys():
            return util.t_type, exp_type, e_name
    return None, None, None


# Return the type variable and fields information of a datatype
def lookup_fields(dt_name: str) -> List[Tuple[str, str]]:
    return type_dict[dt_name]
