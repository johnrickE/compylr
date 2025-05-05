#!/usr/bin/env python3

"""
ComPyLR-RegEx to DFA conversion.
"""

__author__ = 'johnrickE'


from fsa import *

from parser import *


# Set this to True to generate and print the ComPyLR-RegEx parsing table and reduction lookup buffer.
print_parsing_table = False


""" ComPyLR-RegEx Context Free Grammar
    -------------------------------

S' -> Disjunction

Disjunction -> Disjunction '|' Concatenation
Disjunction -> Concatenation

Concatenation -> Concatenation Quantifier
Concatenation -> Quantifier

Quantifier -> Factor
Quantifier -> Factor '*'
Quantifier -> Factor '+'
Quantifier -> Factor '?'

Factor -> 'CHAR'
Factor -> '(' Disjunction ')'
Factor -> '[' Class ']'

Class -> HalfClass '^' HalfClass
Class -> HalfClass

HalfClass -> HalfClass CharacterRange
HalfClass -> CharacterRange

CharacterRange -> 'CHAR' '-' 'CHAR'
CharacterRange -> 'CHAR'
"""


""" Reduction Callbacks """


def accept(terms, context): # S' -> Disjunction
    # Full RegEx has been transformed to an ε-NFA.
    # Now set the initial and final state, and convert the ε-NFA to a DFA.
    nfa, output = context
    q0, q1 = terms[0]
    nfa.initial_state = q0
    nfa.outputs[q1] = {output}
    return nfa.remove_epsilons().get_dfa()


def r1(terms, context): # Disjunction -> Disjunction '|' Concatenation
    # Apply 'a|b' transformation from Thompson's construction.
    nfa, _ = context
    qa, qb = terms[0]
    qc, qd = terms[2]
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    nfa.add_transition(q0, qa, EPSILON)
    nfa.add_transition(q0, qc, EPSILON)
    nfa.add_transition(qb, q1, EPSILON)
    nfa.add_transition(qd, q1, EPSILON)
    return q0, q1


def r2(terms, _): # Disjunction -> Concatenation
    return terms[0]


def r3(terms, context): # Concatenation -> Concatenation Quantifier
    # Apply 'ab' transformation from Thompson's construction.
    nfa, _ = context
    qa, qb = terms[0]
    qc, qd = terms[1]
    nfa.add_transition(qb, qc, EPSILON)
    return qa, qd


def r4(terms, _): # Concatenation -> Quantifier
    return terms[0]


def r5(terms, _): # Quantifier -> Factor
    return terms[0]


def r6(terms, context): # Quantifier -> Factor '*'
    # Apply 'a*' transformation from Thompson's construction.
    nfa, _ = context
    qa, qb = terms[0]
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    nfa.add_transition(q0, q1, EPSILON)
    nfa.add_transition(qb, qa, EPSILON)
    nfa.add_transition(q0, qa, EPSILON)
    nfa.add_transition(qb, q1, EPSILON)
    return q0, q1


def r7(terms, context): # Quantifier -> Factor '+'
    # Apply 'a+' transformation from Thompson's construction.
    nfa, _ = context
    qa, qb = terms[0]
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    nfa.add_transition(q0, qa, EPSILON)
    nfa.add_transition(qb, q1, EPSILON)
    nfa.add_transition(qb, qa, EPSILON)
    return q0, q1


def r8(terms, context): # Quantifier -> Factor '?'
    # Apply 'a?' transformation from Thompson's construction.
    nfa, _ = context
    qa, qb = terms[0]
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    nfa.add_transition(q0, qa, EPSILON)
    nfa.add_transition(qb, q1, EPSILON)
    nfa.add_transition(q0, q1, EPSILON)
    return q0, q1


def r9(terms, context): # Factor -> 'CHAR'
    # Apply terminal transformation from Thompson's construction.
    nfa, _ = context
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    nfa.add_transition(q0, q1, terms[0])
    return q0, q1


def r10(terms, _): # Factor -> '(' Disjunction ')'
    return terms[1]


def r11(terms, context): # Factor -> '[' Class ']'
    # Apply terminal transformation from Thompson's construction for all symbols in the character class.
    nfa, _ = context
    q0 = nfa.add_state()
    q1 = nfa.add_state()
    for c in terms[1]:
        nfa.add_transition(q0, q1, c)
    return q0, q1


def r12(terms, _): # Class -> HalfClass '^' HalfClass
    return terms[0].difference(terms[2])


def r13(terms, _): # Class -> HalfClass
    return terms[0]


def r14(terms, _): # HalfClass -> HalfClass CharacterRange
    chars = terms[0]
    chars.update(terms[1])
    return chars


def r15(terms, _): # HalfClass -> CharacterRange
    return terms[0]


def r16(terms, _): # CharacterRange -> 'CHAR' '-' 'CHAR'
    return set([c for c in range(terms[0], 1 + terms[2])])


def r17(terms, _): # CharacterRange -> 'CHAR'
    return set([terms[0]])


""" Terminal Symbols + Lexer Code """


TERMINALS = TerminalSet()

BAR = TERMINALS.add()
ASTERISK = TERMINALS.add()
PLUS = TERMINALS.add()
QUESTION = TERMINALS.add()
CHAR = TERMINALS.add()
LPAREN = TERMINALS.add()
RPAREN = TERMINALS.add()
LSQUARE = TERMINALS.add()
RSQUARE = TERMINALS.add()
CARET = TERMINALS.add()
HYPHEN = TERMINALS.add()


# These characters must be escaped by '\' in order to be interpreted as normal characters.
SPECIAL_CHARS = {
    '|': BAR,
    '*': ASTERISK,
    '+': PLUS,
    '?': QUESTION,
    '(': LPAREN,
    ')': RPAREN,
    '[': LSQUARE,
    ']': RSQUARE,
    '^': CARET,
    '-': HYPHEN
}

HEXADECIMAL_CHARS = '0123456789abcdefABCDEF'


def get_codepoint(c: str):
    """
    Gets the codepoint of the specified character. This function also handles escaped characters.

    :param c    A character returned by the lexer.

    :return The codepoint of character c.
    """
    if c == '\\n':
        return ord('\n')
    if c == '\\t':
        return ord('\t')
    if c.startswith('\\x'):
        return int('0x' + c[2:], base=16)
    if c.startswith('\\'):
        return ord(c[1])
    return ord(c[0])


class Lexer:
    """
    Hand-written ComPyLR-RegEx lexer that handles escaped characters.
    """

    def __init__(self, source):
        """
        Constructs a new Lexer that wraps the given input.

        :param source   The raw input.
        """
        self.source = source
        self.position = 0
    
    def lex(self):
        """
        Returns the next token in the stream.

        :return A tuple containing the terminal symbol as well as the codepoint of the character.
        """
        if self.position >= len(self.source):
            return END, None
        state = self.state0
        prev_position = self.position
        while state is not None:
            state = state(self.consume())
        value = self.source[prev_position:self.position]
        return SPECIAL_CHARS.get(value, CHAR), get_codepoint(value)

    def consume(self):
        """
        Consumes an input character.

        :return The consumed character.
        """
        c = self.source[self.position]
        self.position += 1
        return c
    
    """ Each of the following member functions implement a state in the lexer's automaton. """

    def state0(self, c):
        if c == '\\':
            return self.state1
        return None

    def state1(self, c):
        if c == 'x':
            return self.state2
        return None

    def state2(self, c):
        if c in HEXADECIMAL_CHARS:
            return self.state3
        raise LexerError('Invalid character')

    def state3(self, c):
        if c in HEXADECIMAL_CHARS:
            return None
        raise LexerError('Invalid character')


""" Parser Generation Code """


if __name__ == '__main__' and print_parsing_table:
    
    from parsergen import *

    NONTERMINALS = NonTerminalSet()

    Disjunction = NONTERMINALS.add()
    Concatenation = NONTERMINALS.add()
    Quantifier = NONTERMINALS.add()
    Factor = NONTERMINALS.add()
    Class = NONTERMINALS.add()
    HalfClass = NONTERMINALS.add()
    CharacterRange = NONTERMINALS.add()
    
    RULES = [
        (GOAL, [Disjunction], accept), # S' -> Disjunction

        (Disjunction, [Disjunction, BAR, Concatenation], r1),   # Disjunction -> Disjunction '|' Concatenation
        (Disjunction, [Concatenation], r2),                     # Disjunction -> Concatenation

        (Concatenation, [Concatenation, Quantifier], r3),   # Concatenation -> Concatenation Quantifier
        (Concatenation, [Quantifier], r4),                  # Concatenation -> Quantifier

        (Quantifier, [Factor], r5),             # Quantifier -> Factor
        (Quantifier, [Factor, ASTERISK], r6),   # Quantifier -> Factor '*'
        (Quantifier, [Factor, PLUS], r7),       # Quantifier -> Factor '+'
        (Quantifier, [Factor, QUESTION], r8),   # Quantifier -> Factor '?'

        (Factor, [CHAR], r9), # Factor -> 'CHAR'
        (Factor, [LPAREN, Disjunction, RPAREN], r10),   # Factor -> '(' Disjunction ')'
        (Factor, [LSQUARE, Class, RSQUARE], r11),       # Factor -> '[' Class ']'

        (Class, [HalfClass, CARET, HalfClass], r12),    # Class -> HalfClass '^' HalfClass
        (Class, [HalfClass], r13),                      # Class -> HalfClass

        (HalfClass, [HalfClass, CharacterRange], r14),  # HalfClass -> HalfClass CharacterRange
        (HalfClass, [CharacterRange], r15),             # HalfClass -> CharacterRange

        (CharacterRange, [CHAR, HYPHEN, CHAR], r16),    # CharacterRange -> 'CHAR' '-' 'CHAR'
        (CharacterRange, [CHAR], r17)                   # CharacterRange -> 'CHAR'
    ]

    generator = ParserGenerator(TERMINALS, NONTERMINALS, RULES)
    generator.print_table()


""" Parser Generator Output """


# Automatically generated parsing table
TABLE = {
    (0, 4): (3, 1),
    (0, 3): (3, 2),
    (0, 1): (3, 3),
    (0, -8): (0, 4),
    (0, -7): (0, 5),
    (0, -10): (0, 6),
    (0, 2): (3, 7),
    (7, -1): (1, 2),
    (7, -3): (1, 2),
    (7, 4): (3, 1),
    (7, -8): (0, 4),
    (7, -7): (0, 5),
    (7, 3): (3, 8),
    (7, -10): (0, 6),
    (6, 7): (3, 9),
    (6, 5): (3, 10),
    (6, -7): (0, 11),
    (6, 6): (3, 12),
    (12, -11): (1, 13),
    (12, -7): (0, 11),
    (12, 7): (3, 13),
    (12, -12): (0, 14),
    (14, 7): (3, 15),
    (14, -7): (0, 16),
    (14, 6): (3, 17),
    (17, -11): (1, 12),
    (17, -7): (0, 16),
    (17, 7): (3, 18),
    (18, -7): (1, 14),
    (18, -11): (1, 14),
    (16, -11): (1, 17),
    (16, -7): (1, 17),
    (16, -13): (0, 19),
    (19, -7): (0, 20),
    (20, -11): (1, 16),
    (20, -7): (1, 16),
    (15, -7): (1, 15),
    (15, -11): (1, 15),
    (13, -7): (1, 14),
    (13, -12): (1, 14),
    (13, -11): (1, 14),
    (11, -12): (1, 17),
    (11, -7): (1, 17),
    (11, -11): (1, 17),
    (11, -13): (0, 21),
    (21, -7): (0, 22),
    (22, -11): (1, 16),
    (22, -7): (1, 16),
    (22, -12): (1, 16),
    (10, -11): (0, 23),
    (23, -7): (1, 11),
    (23, -4): (1, 11),
    (23, -8): (1, 11),
    (23, -5): (1, 11),
    (23, -1): (1, 11),
    (23, -6): (1, 11),
    (23, -3): (1, 11),
    (23, -10): (1, 11),
    (9, -7): (1, 15),
    (9, -12): (1, 15),
    (9, -11): (1, 15),
    (8, -7): (1, 3),
    (8, -3): (1, 3),
    (8, -8): (1, 3),
    (8, -10): (1, 3),
    (8, -1): (1, 3),
    (5, -8): (1, 9),
    (5, -1): (1, 9),
    (5, -6): (1, 9),
    (5, -3): (1, 9),
    (5, -7): (1, 9),
    (5, -10): (1, 9),
    (5, -4): (1, 9),
    (5, -5): (1, 9),
    (4, 3): (3, 24),
    (4, -8): (0, 25),
    (4, 1): (3, 26),
    (4, 4): (3, 27),
    (4, -7): (0, 28),
    (4, -10): (0, 29),
    (4, 2): (3, 30),
    (30, -9): (1, 2),
    (30, -3): (1, 2),
    (30, 4): (3, 27),
    (30, -8): (0, 25),
    (30, 3): (3, 31),
    (30, -7): (0, 28),
    (30, -10): (0, 29),
    (29, 7): (3, 9),
    (29, 5): (3, 32),
    (29, -7): (0, 11),
    (29, 6): (3, 12),
    (32, -11): (0, 33),
    (33, -7): (1, 11),
    (33, -4): (1, 11),
    (33, -8): (1, 11),
    (33, -5): (1, 11),
    (33, -6): (1, 11),
    (33, -9): (1, 11),
    (33, -3): (1, 11),
    (33, -10): (1, 11),
    (28, -8): (1, 9),
    (28, -9): (1, 9),
    (28, -6): (1, 9),
    (28, -3): (1, 9),
    (28, -7): (1, 9),
    (28, -10): (1, 9),
    (28, -4): (1, 9),
    (28, -5): (1, 9),
    (31, -7): (1, 3),
    (31, -9): (1, 3),
    (31, -3): (1, 3),
    (31, -8): (1, 3),
    (31, -10): (1, 3),
    (25, 3): (3, 24),
    (25, -8): (0, 25),
    (25, 1): (3, 34),
    (25, 4): (3, 27),
    (25, -7): (0, 28),
    (25, -10): (0, 29),
    (25, 2): (3, 30),
    (27, -8): (1, 5),
    (27, -7): (1, 5),
    (27, -10): (1, 5),
    (27, -9): (1, 5),
    (27, -3): (1, 5),
    (27, -4): (0, 35),
    (27, -6): (0, 36),
    (27, -5): (0, 37),
    (37, -9): (1, 7),
    (37, -7): (1, 7),
    (37, -3): (1, 7),
    (37, -8): (1, 7),
    (37, -10): (1, 7),
    (36, -3): (1, 8),
    (36, -8): (1, 8),
    (36, -10): (1, 8),
    (36, -9): (1, 8),
    (36, -7): (1, 8),
    (35, -3): (1, 6),
    (35, -8): (1, 6),
    (35, -7): (1, 6),
    (35, -10): (1, 6),
    (35, -9): (1, 6),
    (34, -3): (0, 38),
    (34, -9): (0, 39),
    (39, -6): (1, 10),
    (39, -9): (1, 10),
    (39, -3): (1, 10),
    (39, -10): (1, 10),
    (39, -4): (1, 10),
    (39, -7): (1, 10),
    (39, -8): (1, 10),
    (39, -5): (1, 10),
    (38, 4): (3, 27),
    (38, 3): (3, 24),
    (38, -8): (0, 25),
    (38, -7): (0, 28),
    (38, -10): (0, 29),
    (38, 2): (3, 40),
    (40, -3): (1, 1),
    (40, -9): (1, 1),
    (40, 4): (3, 27),
    (40, -8): (0, 25),
    (40, -7): (0, 28),
    (40, 3): (3, 31),
    (40, -10): (0, 29),
    (24, -9): (1, 4),
    (24, -3): (1, 4),
    (24, -8): (1, 4),
    (24, -10): (1, 4),
    (24, -7): (1, 4),
    (26, -3): (0, 38),
    (26, -9): (0, 41),
    (41, -1): (1, 10),
    (41, -6): (1, 10),
    (41, -3): (1, 10),
    (41, -10): (1, 10),
    (41, -4): (1, 10),
    (41, -7): (1, 10),
    (41, -8): (1, 10),
    (41, -5): (1, 10),
    (1, -8): (1, 5),
    (1, -1): (1, 5),
    (1, -7): (1, 5),
    (1, -10): (1, 5),
    (1, -3): (1, 5),
    (1, -4): (0, 42),
    (1, -6): (0, 43),
    (1, -5): (0, 44),
    (44, -7): (1, 7),
    (44, -3): (1, 7),
    (44, -8): (1, 7),
    (44, -1): (1, 7),
    (44, -10): (1, 7),
    (43, -3): (1, 8),
    (43, -8): (1, 8),
    (43, -10): (1, 8),
    (43, -1): (1, 8),
    (43, -7): (1, 8),
    (42, -3): (1, 6),
    (42, -8): (1, 6),
    (42, -1): (1, 6),
    (42, -7): (1, 6),
    (42, -10): (1, 6),
    (3, -1): (2, 0),
    (3, -3): (0, 45),
    (45, 4): (3, 1),
    (45, 3): (3, 2),
    (45, -8): (0, 4),
    (45, -7): (0, 5),
    (45, -10): (0, 6),
    (45, 2): (3, 46),
    (46, -1): (1, 1),
    (46, -3): (1, 1),
    (46, 4): (3, 1),
    (46, -8): (0, 4),
    (46, 3): (3, 8),
    (46, -7): (0, 5),
    (46, -10): (0, 6),
    (2, -3): (1, 4),
    (2, -8): (1, 4),
    (2, -10): (1, 4),
    (2, -1): (1, 4),
    (2, -7): (1, 4),
}

# Automatically generated reduction lookup buffer
REDUCTIONS = [
    (0,1,accept),
    (1,3,r1),
    (1,1,r2),
    (2,2,r3),
    (2,1,r4),
    (3,1,r5),
    (3,2,r6),
    (3,2,r7),
    (3,2,r8),
    (4,1,r9),
    (4,3,r10),
    (4,3,r11),
    (5,3,r12),
    (5,1,r13),
    (6,2,r14),
    (6,1,r15),
    (7,3,r16),
    (7,1,r17),
]


""" Parser Factory Method """


def get_parser():
    """
    Creates a new ComPyLR-RegEx parser.

    :return A Parser object used to compile regular expressions to DFAs. 
    """
    return Parser(TABLE, REDUCTIONS, lambda source: Lexer(source), lambda output: (NFA(), output))
