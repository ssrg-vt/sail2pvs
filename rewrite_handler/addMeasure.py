#! /usr/bin/env python3

# Automatically construct a measure function for a recursive function
# The auto-generated measure function might be incorrect and need manual modification

from . import util


def construct_measure(args, content):
    for arg in args:
        if arg[util.u_annotation].startswith('list') and 'ENDCASES' in content:
            return 'length(' + arg[util.u_name].strip() + ')'
        if arg[util.u_annotation] == 'nat':
            return arg[util.u_name]
        if arg[util.u_annotation] == 'int' and 'ENDCASES' not in content:
            return 'abs(' + arg[util.u_name].strip() + ')'
    if 'ENDCASES' in content:
        elem = util.caseCondPat.findall(content)[0].strip()
        return elem + ' BY <<'
    return ''


def handle_recursive(arg_list, content):
    measure_function = construct_measure(arg_list, content)
    return '\nMEASURE ' + measure_function

