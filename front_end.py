import sys
import re
from enum import Enum
import jsonpickle # pip install jsonpickle
import json
# TODO GREATER AND LESS IMPLEMENTATION
# TODO implementation of get_val (recursive) and alist and dlist

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
        self.left = None
        self.right = None
        if r_exp is None:
            self.exp_value = l_exp
        else:
            self.left = l_exp
            self.right = r_exp

    def is_atom(self):
        if self.left is None and self.right is None:
            return SExp.get_atom('T')
        else:
            return SExp.get_atom('NIL')

    def car(self):
        if self.left is None:
            raise Exception("CAR is defined for non-atomic expressions")
        else:
            return self.left

    def cdr(self):
        if self.right is None:
            raise Exception("CAR is defined for non-atomic expressions")
        else:
            return self.right

    def is_null(self):
        nil = SExp.get_atom('NIL')
        if self.exp_type == nil.exp_type and self.exp_value == nil.exp_value:
            return SExp.get_atom('T')
        else:
            return SExp.get_atom('NIL')

    def is_int(self):
        if self.exp_type == ExpType.int_atom:
            return SExp.get_atom('T')
        else:
            return SExp.get_atom('NIL')

    @staticmethod
    def equal(s1, s2):
        if s1.left is None and s1.right is None and s2.left is None and s2.right is None:
            if s1.exp_type == ExpType.int_atom and s2.exp_type == ExpType.int_atom:
                if s1.exp_value == s2.exp_value:
                    return SExp.get_atom('T')
                else:
                    return SExp.get_atom('NIL')
            if s1.exp_type == ExpType.symb_atom and s2.exp_type == ExpType.symb_atom:
                if s1.exp_value == s2.exp_value:
                    return SExp.get_atom('T')
                else:
                    return SExp.get_atom('NIL')
            else:
                return SExp.get_atom('NIL')

        else:
            raise Exception('Both arguments for EQ should be atomic')

    @staticmethod
    def cons(s1, s2):
        return SExp(ExpType.non_atom, s1, s2)

    @staticmethod
    def get_atom(symbol):
        return find(decl_symb, symbol)

    @staticmethod
    def plus(s1, s2):
        if s1.exp_type != ExpType.int_atom or s2.exp_type != ExpType.int_atom:
            raise Exception("Both PLUS arguments should be integer atoms")
        else:
            result_value = int(s1.exp_value) + int(s2.exp_value)
            return SExp(ExpType.int_atom, str(result_value))

    @staticmethod
    def minus(s1, s2):
        if s1.exp_type != ExpType.int_atom or s2.exp_type != ExpType.int_atom:
            raise Exception("Both MINUS arguments should be integer atoms")
        else:
            result_value = int(s1.exp_value) - int(s2.exp_value)
            return SExp(ExpType.int_atom, str(result_value))

    @staticmethod
    def times(s1, s2):
        if s1.exp_type != ExpType.int_atom or s2.exp_type != ExpType.int_atom:
            raise Exception("Both TIMES arguments should be integer atoms")
        else:
            result_value = int(s1.exp_value) * int(s2.exp_value)
            return SExp(ExpType.int_atom, str(result_value))

    @staticmethod
    def quotient(s1, s2):
        if s1.exp_type != ExpType.int_atom or s2.exp_type != ExpType.int_atom:
            raise Exception("Both QUOTIENT arguments should be integer atoms")
        else:
            result_value = int(int(s1.exp_value) / int(s2.exp_value))
            return SExp(ExpType.int_atom, str(result_value))

    @staticmethod
    def remainder(s1, s2):
        if s1.exp_type != ExpType.int_atom or s2.exp_type != ExpType.int_atom:
            raise Exception("Both REMAINDER arguments should be integer atoms")
        else:
            result_value = int(int(s1.exp_value) % int(s2.exp_value))
            return SExp(ExpType.int_atom, str(result_value))

    @staticmethod
    def get_val(exp, exp_list):
        if exp_list is list:
            return None
        if exp_list.exp_type != ExpType.non_atom:
            return None
        symb_atom = exp_list.car().car()
        if SExp.equal(exp, symb_atom) == SExp.get_atom('T'):
            return exp_list.car().cdr()
        else:
            return SExp.get_val(exp, exp_list.cdr())

    # def get_val(exp, exp_list):
    #     for item in exp_list:
    #         symb_atom = item.car()
    #         if SExp.equal(exp, symb_atom) == SExp.get_atom('T'):
    #             return item.cdr()
    #     return None

    @staticmethod
    def add_pairs(para_list, arg_list, alist):
        if para_list.is_null() == SExp.get_atom('T'):
            return alist
        else:
            s1 = SExp.cons(para_list.car(), arg_list.car())
            s2 = SExp.add_pairs(para_list.cdr(), arg_list.cdr(), alist)
            return SExp.cons(s1, s2)
        return

def eval_exp(exp, alist,dlist):
    t = SExp.get_atom('T')
    nil = SExp.get_atom('NIL')
    if exp.is_atom() == t:
        if exp.is_int() == t:
            return exp
        if SExp.equal(exp, t) == t:
            return t
        if SExp.equal(exp, nil) == t:
            return nil
        value = SExp.get_val(exp, alist)
        if value is not None:
            return value
        else:
            raise Exception("Unbound ATOM!")
    car_exp = exp.car()
    if car_exp.is_atom() == t:
        if car_exp == SExp.get_atom('QUOTE'):
            cadr_exp = exp.cdr().car()
            return cadr_exp
        if car_exp == SExp.get_atom('COND'):
            return evcon(exp.cdr(), alist, dlist)
        if car_exp == SExp.get_atom('DEFUN'):
            # (DEFUN  F  (p1 ... pn)  fb) : add (F . ((p1 ... pn) . fb)) to d-list.
            #  DEFUN.(F.((P1.(PN.NIL)).(FB.NIL))))
            # (DEFUN.(F.((P1.(P2.(P3.(PN.NIL)))).(FB.NIL))))
            # eg (DEFUN F (P1 P2 P3 PN) FB)
            function_name = exp.cdr().car()
            function_body = exp.cdr().cdr().cdr().car()
            parameters = exp.cdr().cdr().car()
            exp_name = function_name
            exp_value = SExp(ExpType.non_atom, parameters, function_body)
            global d_list
            d_list = SExp.cons(SExp(ExpType.non_atom, exp_name, exp_value) , dlist)
            return SExp.get_atom('FUNCTION ADDED!')
        else:
            return apply(car_exp, evlis(exp.cdr(), alist, dlist) , alist, dlist)
    else:
        raise Exception("ERROR: invalid lisp expression: atom is expected ")


def apply(function_name, arg_list, alist, dlist):
    if function_name.is_atom() == SExp.get_atom('T'):
        if function_name == SExp.get_atom('CAR'):
            return arg_list.car().car()
        if function_name == SExp.get_atom('CDR'):
            return arg_list.car().cdr()
        if function_name == SExp.get_atom('CONS'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.cons(car_arg_list, cadr_arg_list)
        if function_name == SExp.get_atom('ATOM'):
            return arg_list.car().is_atom()
        if function_name == SExp.get_atom('NULL'):
            return arg_list.car().is_null()
        if function_name == SExp.get_atom('EQ'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.equal(car_arg_list,cadr_arg_list)
        if function_name == SExp.get_atom('PLUS'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.plus(car_arg_list, cadr_arg_list)
        if function_name == SExp.get_atom('MINUS'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.minus(car_arg_list, cadr_arg_list)
        if function_name == SExp.get_atom('TIMES'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.times(car_arg_list, cadr_arg_list)
        if function_name == SExp.get_atom('QUOTIENT'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.quotient(car_arg_list, cadr_arg_list)
        if function_name == SExp.get_atom('REMAINDER'):
            car_arg_list = arg_list.car()
            cadr_arg_list = arg_list.cdr().car()
            return SExp.remainder(car_arg_list, cadr_arg_list)

        else:
            user_def_fun = SExp.get_val(function_name, dlist)
            fun_body = user_def_fun.cdr()
            fun_parameters = user_def_fun.car()
            # TODO ADD PAIRS
            new_alist = SExp.add_pairs(fun_parameters, arg_list, alist)
            return eval_exp(fun_body, new_alist, dlist)

    else:
        raise Exception('Error in Applying Function: function_name is not atomic')


def evlis(par_list, alist, dlist):
    if par_list.is_null() == SExp.get_atom('T'):
        return SExp.get_atom('NIL')
    else:
        s1 =eval_exp(par_list.car(), alist, dlist)
        s2 =evlis(par_list.cdr(), alist, dlist)
        return SExp.cons(s1,  s2)


def evcon(be, alist, dlist): # be is of form ((b1 e1) ... (bn en))
    if be.is_null() == SExp.get_atom('T'):
        raise Exception("Invalid boolean in if clause")
    caar_be = be.car().car()
    if eval_exp(caar_be, alist, dlist) == SExp.get_atom('T'):
        cadar_be =be.car().cdr().car()
        return eval_exp(cadar_be, alist, dlist)
    else:
        return evcon(be.cdr(), alist, dlist)


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




def list_parser(exp):
    nxt_token = CkNextToken(exp)
    if nxt_token == TokenType.right_parenth:
        return SExp.get_atom('NIL')
    if nxt_token == TokenType.space:
        if check_next_next_token(exp) != TokenType.right_parenth:
            skip_token(exp)
            s1 = parser(exp)
            s2 = list_parser(exp)
            return SExp.cons(s1, s2)
        else:
            skip_token(exp) # skipping space in these (1 ) expressions
            return SExp.get_atom('NIL')

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
            return SExp.get_atom('NIL')
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
        return SExp.cons(s1, s2)

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
            print("\n")
            print('> ', end='')
            evaluated_exp = eval_exp(sexp,a_list,d_list)
            output(evaluated_exp)
            print("\n----------------------")
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
decl_symb.append(SExp(ExpType.symb_atom, 'DEFUN'))
decl_symb.append(SExp(ExpType.symb_atom, 'QUOTE'))
decl_symb.append(SExp(ExpType.symb_atom, 'COND'))
decl_symb.append(SExp(ExpType.symb_atom, 'FUNCTION ADDED!'))
a_list=SExp.get_atom('NIL')
d_list=SExp.get_atom('NIL')
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
#tokenized_list =[['(', 'EQ', ' ', '2', ' ', '2', ')'], ['(', 'EQ', ' ', '1', ' ', '2', ')']]#
#tokenized_list = [['(', 'PLUS', ' ', '3', ' ', '4', ')']]
#tokenized_list = [['(', 'DEFUN', ' ', 'SILLY', ' ', '(', 'A', ' ', 'B', ')', ' ', '(', 'PLUS', ' ', 'A', ' ', 'B', ')', ')'], ['(', 'SILLY', ' ', '5', ' ', '6', ')']]
print(tokenized_list)
print("===================================================================")
print("Accepted Expressions For Second Pass Checking:")
print_accepted_exp(tokenized_list)

print("===================================================================")
print("Second Pass Checking:\n")
obj=parse_list(tokenized_list)
print("\n===================================================================")
