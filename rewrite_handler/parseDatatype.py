#! /usr/bin/env python3

# -*- coding: utf-8 -*-

from . import util


def parse_datatype(var_dict, lines):
    name = util.split_sep(lines[0], ':')[0].split('[')[0]
    type_variables = util.get_type_variables(lines[0])
    contents = {}
    field_dec = ''
    for line in lines:
        if 'DATATYPE' in line or 'BEGIN' in line:
            continue
        elif '?' in line:
            field_dec += line
            field_dec = field_dec.replace(' ', '').replace('\n', '')
            field_split = util.split_sep_bk(field_dec, ':')[0].strip()
            constructor = field_split.split('(')[0].strip()
            arg_list = util.extract_bk_content(field_split)
            field_type = util.argSep.join(
                map(lambda arg: util.parse_args(var_dict, arg.split('(', 1)[1].rsplit(')', 1)[0].strip())[1], arg_list))
            field_type = field_type.replace(' ', '')
            contents[constructor] = field_type
            field_dec = ''
        else:
            field_dec += line
    return name, (type_variables, contents)


if __name__ == '__main__':
    print(parse_datatype({}, '''option[T:TYPE] : DATATYPE
    BEGIN
        Some(t: T): Some?
        None: None?'''.split('\n')))

