#! /usr/bin/env python3

from . import util
from . import parseFiles
from typing import List, Tuple


def build_case_expr(cond: str, rules: List[List[str]])->str:
    result = 'CASES ' + cond + ' OF\n'

    if rules[-1][0] == 'ELSE':
        result += ',\n'.join(map(lambda s: '    ' + s[0] + ': ' + s[1] + '', rules[:-1]))
        result += '\n    ' + rules[-1][0] + ' ' + rules[-1][1]
    else:
        result += ',\n'.join(map(lambda s: '    ' + s[0] + ': ' + s[1] + '', rules))
    result += '\nENDCASES'
    return result


def build_table_expr(cond, rules):
    result = 'TABLE ' + cond + '\n'
    result += '\n'.join(map(lambda s: '  | ' + s[0] + ' | ' + s[1] + ' ||', rules))
    result += '\nENDTABLE'
    return result


# Invalid cases expression in PVS
def is_valid_case(fields, case_rules: List[List[str]])->bool:
    util.logger.debug('------------is_valid_case------------')
    pattern_exprs = list(map(lambda x: x[0], case_rules))
    condNames, condArgs = zip(*list(map(lambda x: util.split_fun_app(x), pattern_exprs)))
    if util.has_dup(condNames):
        util.logger.info('These are duplicate fields')
        return False
    field_num = len(fields)
    case_num = len(case_rules)
    if field_num != case_num and 'ELSE' not in condNames:
        util.logger.info('The number of fields is not equal to case number')
        return False
    for constr_name, case_arg in zip(condNames, condArgs):
        if constr_name != 'ELSE':
            field_annot = util.split_arg_list(fields[constr_name], '[')
            arg_list = util.split_sep_bk(case_arg, ',')
            if len(field_annot) != len(arg_list):
                util.logger.info('The number of field arguments is different from the number of real arguments')
                return False
            else:
                for arg in arg_list:
                    if arg != '' and not util.idPat.search(arg.strip()):
                        util.logger.info('The argument is not a valid ID')
                        return False
    return True


# Replace variable names in multiple expression
def replace_rule_first_variable(exprs: List[List[str]], nv_args: List[str]):
    n = len(exprs)
    for i in range(n):
        r = exprs[i]
        ov_args = util.extract_tuple_first_arg(r[0])
        for j in range(len(ov_args)):
            exprs[i][1] = util.replace_expr_variable(r[1], ov_args[j], nv_args[j])


def construct_tuple_datatype_expr(tup_idx: int, fields, case_cond: str, constr_list: List[str], tuples, case_rules, arg_list, else_exp):
    util.logger.debug('------------construct_tuple_datatype_expr------------')
    util.logger.debug('case condition:')
    util.logger.debug(case_cond)
    result = 'CASES ' + case_cond + ' OF \n'
    for nv in constr_list:
        sel_expr, nv_args = util.construct_field_expression(tup_idx, nv, fields[nv])
        tmp_case_rules = list(
            filter(lambda x: util.split_arg_list(x[0])[0].split('(', 1)[0].strip() == nv, case_rules))
        util.logger.debug('Before replace_rule_first_variable')
        util.logger.debug(tmp_case_rules)
        util.logger.debug(nv_args)
        replace_rule_first_variable(tmp_case_rules, nv_args)
        util.logger.debug('After replace_rule_first_variable')
        util.logger.debug(tmp_case_rules)
        if len(tuples) > 0:
            tmp_case_rules = list(map(lambda x: [util.remove_tuple_first_element(x[0]), x[1]], tmp_case_rules))
            case_expr = construct_tuple_expr(tup_idx + 1, tuples, tmp_case_rules, arg_list, else_exp)
        else:
            case_expr = tmp_case_rules[0][1]
        result += '  ' + sel_expr + ': ' + util.block_indent(case_expr) + ',\n'
    result = result.rsplit(',', 1)[0]
    if len(constr_list) < len(fields):
        result += '\n   ELSE ' + else_exp
    result += '\nENDCASES'
    return result


# Construct a new expression for the tuple type following PVS rules
def construct_tuple_expr(tup_idx: int, tuples: List[str], case_rules: List[List[str]], arg_list: List[Tuple[str, str]], else_exp: str)->str:
    if len(tuples) == 0:
        return ''
    pattern_exprs = list(map(lambda x: x[0], case_rules))
    case_arg_list: List[List[str]] = list(map(lambda s: util.split_arg_list(s), pattern_exprs))
    t = tuples[0]
    new_tuples = tuples[1:]
    var_list: List[str] = [cl[0] for cl in case_arg_list]
    var_type, type_name, dt_name = parseFiles.exp_type_string(t, arg_list)
    util.logger.debug('------------construct_tuple_expr------------')
    util.logger.debug('following tuple: ')
    util.logger.debug(tuples)
    util.logger.debug('case_arg_list:')
    util.logger.debug(case_arg_list)
    util.logger.debug('variable lists:')
    util.logger.debug(var_list)
    util.logger.debug('case_rules:')
    util.logger.debug(case_rules)
    util.logger.debug('var_type:')
    util.logger.debug(var_type)
    parentheses_t = '(' + t
    tmp_rules = list(filter(lambda x: x[0].startswith(parentheses_t), case_rules))
    if len(tmp_rules) == len(case_rules):
        if len(new_tuples) > 0:
            tmp_case_rules = list(map(lambda x: [util.remove_tuple_first_element(x[0]), x[1]], case_rules))
            case_expr = construct_tuple_expr(tup_idx + 1, new_tuples, tmp_case_rules, arg_list, else_exp)
        else:
            case_expr = case_rules[0][1]
        return case_expr
    if var_type == util.t_type:
        fields = parseFiles.lookup_fields(dt_name)[1]
        nv_list = list(set(map(lambda x: x.split('(', 1)[0].strip(), var_list)))
        nv_field_list = [nv for nv in nv_list if nv in fields]
        nv_not_field_list = [nv for nv in nv_list if nv not in fields]
        if nv_not_field_list:
            util.logger.debug('construct_tuple_expr nv_not_field_list')
            util.logger.debug(tuples)
            util.logger.debug(case_rules)
            util.logger.debug(arg_list)
            result = ''
            if nv_field_list:
                result = construct_tuple_datatype_expr(tup_idx, fields, t, nv_field_list, new_tuples, case_rules, arg_list, else_exp)
                result += '\n  ELSE '
            tmp_case_rules = []
            for nv in nv_not_field_list:
                tmp = list(filter(lambda x: util.split_arg_list(x[0])[0].split('(', 1)[0].strip() == nv, case_rules))
                replace_rule_first_variable(tmp, [nv])
                tmp_case_rules.extend(tmp)
            if len(new_tuples) > 0:
                tmp_case_rules = list(map(lambda x: [util.remove_tuple_first_element(x[0]), x[1]], tmp_case_rules))
                case_expr = construct_tuple_expr(tup_idx + 1, new_tuples, tmp_case_rules, arg_list, else_exp)
            else:
                case_expr = tmp_case_rules[0][1]
            result += util.block_indent(case_expr)
        else:
            util.logger.debug('construct_tuple_expr nv_field_list')
            util.logger.debug(tuples)
            util.logger.debug(case_rules)
            util.logger.debug(arg_list)
            result = construct_tuple_datatype_expr(tup_idx, fields, t, nv_field_list, new_tuples, case_rules, arg_list, else_exp)
    else:
        util.logger.debug('construct_tuple_expr unknown type')
        nv_list = list(set(map(lambda x: x.split('(', 1)[0].strip(), var_list)))
        util.logger.debug('new variable list:')
        util.logger.debug(nv_list)
        util.logger.debug('case rules:')
        util.logger.debug(case_rules)
        cond_list = []
        for nv in nv_list:
            tmp_case_rules = list(filter(lambda x: util.split_arg_list(x[0])[0].split('(', 1)[0].strip() == nv, case_rules))
            util.logger.debug('temp case rules:')
            util.logger.debug(tmp_case_rules)
            if len(new_tuples) > 0:
                tmp_case_rules = list(map(lambda x: [util.remove_tuple_first_element(x[0]), x[1]], tmp_case_rules))
                util.logger.debug('temp case rules after remove_tuple_first_element:')
                util.logger.debug(tmp_case_rules)
                temp = construct_tuple_expr(tup_idx + 1, new_tuples, tmp_case_rules, arg_list, else_exp)
            else:
                temp = tmp_case_rules[0][1]
            cond_list.append('IF ' + t + ' = ' + nv + ' THEN ' + util.block_indent(temp))
        result = ' \n  ELSE '.join(cond_list) + '\nENDIF' * len(nv_list)
    return result


# Construct a new case expression for datatype
def construct_case_expr(tup_idx: int, cond_type: str, tvs: List[str], constructor: str, annotation: List[str],
                        case_rules: List[List[str]], arg_list: List[Tuple[str, str]], else_exp: str):
    util.logger.debug('------------construct_case_expr------------')
    if len(annotation) == 0:
        return case_rules[0]
    sel_expr, nv_args = util.construct_field_expression(tup_idx, constructor, annotation)
    util.logger.debug('selection expression:')
    util.logger.debug(sel_expr)
    util.logger.debug('new variable arguments:')
    util.logger.debug(nv_args)
    tv_insts = util.split_sep(util.extract_content(cond_type, '['), ',')
    annots = util.split_arg_list(annotation, '[')
    for i in range(len(nv_args)):
        nv = nv_args[i]
        annot = annots[i]
        arg_list.append((nv, util.replace_multiple(annot, tvs, tv_insts)))
    util.logger.debug('argument list:')
    util.logger.debug(arg_list)
    result = sel_expr + ' : '
    new_case_rules = list(map(lambda x: ['(' + x[0].split('(', 1)[1], x[1]], case_rules))
    new_pattern = construct_tuple_expr(tup_idx + 1, nv_args, new_case_rules, arg_list, else_exp)
    result += util.block_indent(new_pattern)
    return result


def construct_datatype_expr(tup_idx: int, dt_name: str, cond: str, cond_type: str, rules: List[List[str]], arg_list: List[Tuple[str, str]], else_exp: str):
    util.logger.debug('------------construct_datatype_expr------------')
    tvs, fields = parseFiles.lookup_fields(dt_name)
    util.logger.debug('datatype name:')
    util.logger.debug(dt_name)
    util.logger.debug('type variables:')
    util.logger.debug(tvs)
    util.logger.debug('datatype fields:')
    util.logger.debug(fields)
    util.logger.debug('rules:')
    util.logger.debug(rules)
    if not is_valid_case(fields, rules):
        new_cases = []
        for field_name in fields:
            cases = list(filter(lambda s: s[0].split('(', 1)[0] == field_name, rules))
            if len(cases) != 0:
                util.logger.debug('datatype condition:')
                util.logger.debug(cond)
                util.logger.debug('datatype condition type:')
                util.logger.debug(cond_type)
                util.logger.debug('argument list:')
                util.logger.debug(arg_list)
                util.logger.debug('datatype cases:')
                util.logger.debug(cases)
                new_case_rule = construct_case_expr(tup_idx, cond_type, tvs, field_name, fields[field_name], cases, arg_list, else_exp)
                new_cases.append(new_case_rule)
        if rules[-1][0] == 'ELSE':
            new_cases.append(rules[-1])
        result = build_case_expr(cond, new_cases)
    else:
        result = build_case_expr(cond, rules)
    return result


# Reconstruct the case expression following certain limitations
def combine_exp(cond, rules, arg_list):
    exp_type, type_name, dt_name = parseFiles.exp_type_string(cond, arg_list)
    else_exp = retrieve_else_exp(rules)
    if exp_type == util.t_type:
        result = construct_datatype_expr(0, dt_name, cond, type_name, rules, arg_list, else_exp)
    elif exp_type == util.t_tuple and cond.strip().startswith('('):
        tuples = util.split_arg_list(cond)
        result = construct_tuple_expr(0, tuples, rules, arg_list, else_exp)
    elif exp_type == util.t_tuple:
        tuple_len = len(util.split_arg_list(type_name, '['))
        tuples = list(map(lambda i: util.generate_new_variable(0, i), list(range(tuple_len))))
        new_exp = construct_tuple_expr(0, tuples, rules, arg_list, else_exp)
        result = 'LET (' + ', '.join(tuples) + ') = ' + cond + ' IN ' + new_exp
    elif len(rules) == 1 and rules[0][0] == cond:
        result = rules[0][1]
    else:
        result = build_table_expr(cond, rules)
    return result


def retrieve_else_exp(rules: List[Tuple[str, str]]):
    else_exp_list = list(filter(lambda x: x[0][0].strip() == 'ELSE', rules))
    if len(else_exp_list) == 0:
        return ''
    elif len(else_exp_list) == 1:
        return else_exp_list[0][1]
    return None


def split_pattern(content: str)->Tuple[str, List[Tuple[str, str]]]:
    contents = content.split('CASES', 1)[1].rsplit('ENDCASES', 1)[0].strip().split('OF', 1)
    cond = contents[0].strip()
    cases = util.split_sep_bk(contents[1].strip(), ',')
    case_rules = list(map(lambda s: util.split_case_line(s), cases))
    return cond, case_rules


def rewrite_pattern(exp: str, arg_list: List[List[str]])->str:
    if exp.startswith('CASES '):
        try:
            util.logger.debug('------------Rewrite_pattern------------')
            util.logger.debug(exp)
            (cond, rules) = split_pattern(exp)
            new_rules = []
            for rule in rules:
                new_rules.append([rule[0], rewrite_pattern(rule[1], arg_list)])
            return combine_exp(cond, new_rules, arg_list)
        except:
            util.logger.debug('Cannot rewrite the pattern for the expression:')
            util.logger.debug(exp)
            return exp
    return exp

