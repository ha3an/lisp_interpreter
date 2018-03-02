import sys
import re
from enum import Enum
import jsonpickle # pip install jsonpickle
import json

decl_symb = []



class TokenType(Enum):
    left_parenth = 1
    right_parenth = 2
    period = 3
    integer = 4
    identifier = 5
    space = 6



class ExpType(Enum):
    int_atom = 1
    symb_atom = 2
    non_atom = 3


class SExp:
    def __init__(self, exp_type, l_exp, r_exp=None):
        self.exp_type = exp_type

        if r_exp is None:
            self.exp_value = l_exp
        else:
            self.left = l_exp
            self.right = r_exp
            # if l_exp.exp_type != ExpType.non_atom:
            #     self.left = SExp(l_exp.exp_type, l_exp.exp_value)
            # else:
            #     self.left = SExp(l_exp.exp_type, l_exp.left, l_exp.right)
            # if r_exp.exp_type != ExpType.non_atom:
            #     self.right = SExp(r_exp.exp_type, r_exp.exp_value)
            # else:
            #     self.right = SExp(r_exp.exp_type, r_exp.left, r_exp.right)


def read():
    buf = []
    seen_first_dollar = False
    while True:
        char = sys.stdin.read(1)
        if not char: # EOF
            break
        if char == '$' and seen_first_dollar:
            buf.pop() # chop the last minus
            break # seen -1
        else:
            seen_first_dollar = (char == '$')
            buf.append(char)
    return buf


def slicer(my_list):
    sectioning_list=[];
    expression=1;
    while True:
        try:
            index = my_list.index('$')
            sectioning_list.append(my_list[:index])
            my_list = my_list[index+1:]
            expression += 1
        except:
            if len(my_list) > 1:
                print("no $ sign, ignoring expression number", expression)
                break
            else:
                break
    return sectioning_list


def scan_illegal_character(exp_list):
    filtered_exp_list = [];
    for exp in exp_list:
        string = ''.join(exp)
        string = re.sub(' +', '0', string)
        string = re.sub('\)+', '0', string)
        string = re.sub('\(+', '0', string)
        string = re.sub('\.+', '0', string)
        string = re.sub('\+', '0', string)
        string = re.sub('\-', '0', string)

        if re.match('^[a-zA-Z0-9]+$', string):
            filtered_exp_list.append(list(''.join(exp).lstrip().rstrip()))
        else:
            print("Illegal character in expression [%s]" % ''.join(exp))

    return filtered_exp_list


def remove_blank(exp_list):
    string = ''.join(exp_list)
    string = re.sub(r"\s+", " ", string)
    string = re.sub(' +', ' ', string)
    return list(string)


def is_valid_token(token):
    str_token=''.join(token)
    if not re.match('^[-+]?[0-9]+$', str_token):
        if str_token[0].isdigit():
            return False
        if re.match('[-+]', str_token):
            return False
    return True


def tokenizer(exp_list):
    tokenized_list = []
    for exp in exp_list:
        add_exp = True
        tokenized_exp = []
        temp = []
        for char in exp:
            if char == '(' or char == ')' or char == '.' or char == ' ':
                if len(temp) != 0:
                    if is_valid_token(temp):
                        tokenized_exp.append(''.join(temp).upper())
                        temp.clear()
                    else:
                        print("invalid identifier < %s > in expression [%s]" % (''.join(temp), ''.join(exp)))
                        add_exp = False
                        break
                tokenized_exp.append(char)
            else:
                temp.append(char)
        if add_exp:
            if len(temp) > 0:
                if is_valid_token(temp):
                    tokenized_exp.append(''.join(temp).upper())
                    temp.clear()
                else:
                    print("invalid identifier < %s > in expression [%s]" % (''.join(temp), ''.join(exp)))
                    return tokenized_list

            tokenized_list.append(tokenized_exp)
    return tokenized_list


def pre_processing(exp_list):
    return tokenizer(scan_illegal_character(slicer(remove_blank(exp_list))))


def CkNextToken(exp):
    char = exp[0]
    if char ==' ':
        return TokenType.space
    if char =='(':
        return TokenType.left_parenth
    if char == ')':
        return TokenType.right_parenth
    if char == '.':
        return TokenType.period
    if re.match('^[-+]?[0-9]+$',char):
        return TokenType.integer
    return TokenType.identifier


def check_next_next_token(exp):
    if len(exp) < 2:
        return TokenType.space
    else:
        temp_token = get_first_token(exp)
        skip_token(exp)
        next_next_token = CkNextToken(exp)
        exp.insert(0,temp_token)
        return next_next_token

def skip_token(exp):
    exp.pop(0)


def get_first_token(exp):
    return exp[0]


def find(id_list, identifier):
    for item in id_list:
        if item.exp_value == identifier:
            return item
    return None


def get_nil():
    return find(decl_symb, 'NIL')

def list_parser(exp):
    nxt_token = CkNextToken(exp)
    if nxt_token == TokenType.right_parenth:
        return get_nil()
    if nxt_token == TokenType.space:
        if check_next_next_token(exp) != TokenType.right_parenth:
            skip_token(exp)
            s1 = parser(exp)
            s2 = list_parser(exp)
            return SExp(ExpType.non_atom, s1, s2)
        else:
            skip_token(exp) # skipping space in these (1 ) expressions
            return get_nil()

    else:
        raise Exception('expects dot or space between two expressions ')


def parser(exp):
    if len(exp)==0:
        raise Exception('missing parentheses for expression ')

    nxt_token = CkNextToken(exp)
    if nxt_token == TokenType.right_parenth or nxt_token == TokenType.period:
        raise Exception('invalid  starting char for expression ')

    if nxt_token == TokenType.left_parenth:
        skip_token(exp)
        if CkNextToken(exp) == TokenType.space:
            skip_token(exp)
        if CkNextToken(exp) == TokenType.right_parenth:
            skip_token(exp)
            return get_nil()
        s1 = parser(exp)
        nxt_token = CkNextToken(exp)

        if nxt_token != TokenType.period:
            nxt_nxt_token = check_next_next_token(exp)
            if nxt_nxt_token != TokenType.period:
                s2 = list_parser(exp)
            else:
                skip_token(exp)  # skipping space in these (1 .2) expressions
                skip_token(exp)  # skipping period
                if CkNextToken(exp) == TokenType.space:
                    skip_token(exp)  # skipping space in these (1 . 2) expressions
                s2 = parser(exp)
        else:

            skip_token(exp)
            if CkNextToken(exp) == TokenType.space:
                skip_token(exp) # skipping space in these (1. 2) expressions
            s2 = parser(exp)

        nxt_token = CkNextToken(exp)
        if nxt_token == TokenType.space:
            skip_token(exp)
            nxt_token = CkNextToken(exp)
        if nxt_token != TokenType.right_parenth:
            raise Exception('missing parentheses at end of expression ')
        skip_token(exp)
        return SExp(ExpType.non_atom, s1, s2)

    if nxt_token == TokenType.integer:
        s1 = SExp(ExpType.int_atom, get_first_token(exp))
        skip_token(exp)
        return s1
    if nxt_token == TokenType.identifier:
        global decl_symb
        symb = find(decl_symb, get_first_token(exp))
        if symb is None:
            s1 = SExp(ExpType.symb_atom, get_first_token(exp))
            decl_symb.append(s1)
            skip_token(exp)
            return s1
        else:
            skip_token(exp)
            return symb
        return


def output(sexp):
    if sexp.exp_type == ExpType.non_atom:
        print('(', end='')
        output(sexp.left)
        print('.', end='')
        output(sexp.right)
        print(')', end='')
    else:
        print(str(sexp.exp_value), end='')



def parse_list(exp_list):
    for idx, exp in enumerate(exp_list):
        try:
            sexp=parser(exp)
            if len(exp) != 0:
                raise Exception('invalid characters at end of expressions ')
            output(sexp)
            print()
            #serialized = jsonpickle.encode(obj)
            #print(json.dumps(json.loads(serialized), indent=4))
        except Exception as error_msg:
            print("line "+str(idx+1)+': '+str(error_msg))

def print_accepted_exp(tokenized_list):
    for idx, exp in enumerate(tokenized_list):
        print(str(idx+1)+': ' +''.join(exp))

print("Note: code should be terminated with $$")

decl_symb.append(SExp(ExpType.symb_atom, 'NIL'))
decl_symb.append(SExp(ExpType.symb_atom, 'T'))

input_list = []
input_list = read()
#input_list =['(','m','2','.','3', ')', '$']
#input_list = ['m','m','$']
#input_list=['3','(','$']
#input_list =['(', 's1',' ','s2', ')', '$']
#input_list =['(', 's1', ')', '$']
#input_list =['(','1','.','3',')','.','(','2','.','3',')','$']
#input_list =['(','b1','.','1',')','$','(','1','.','b1',')','$']

print("===================================================================")
print("First Pass Checking:")
tokenized_list = pre_processing(input_list)
#tokenized_list =[['(', ' ', ')']];
#tokenized_list = [['(', '1',' ','.',' ','2', ')']]
#tokenized_list =[['(', '1', ' ', ')']];
#print(tokenized_list)
print("===================================================================")
print("Accepted Expressions For Second Pass Checking:")
print_accepted_exp(tokenized_list)

print("===================================================================")
print("Second Pass Checking:")
obj=parse_list(tokenized_list)
print("===================================================================")
