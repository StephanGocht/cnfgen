#!/usr/bin/env python
# -*- coding:utf-8 -*-

from __future__ import print_function

__docstring__ =\
"""Utilities to build CNF formulas interesting for proof complexity.

The module `dimacs` contains facilities to generate manipulates dimacs
CNFs, in particular from command line.

Copyright (C) 2012, 2013  Massimo Lauria <lauria@kth.se>
https://github.com/MassimoLauria/cnfgen.git

"""

import sys
import random
import subprocess
from cnfformula import CNF
from cnfformula.utils import dimacs2cnf

def reshuffle(cnf,
              variable_permutation=None,
              clause_permutation=None,
              polarity_flip=None
              ):
    """ Reshuffle the given cnf. Returns a formula logically
    equivalent to the input with the following transformations
    applied in order:

    1. Polarity flips. polarity_flip is a {-1,1}^n vector. If the i-th
    entry is -1, all the literals with the i-th variable change its
    sign.

    2. Variable permutations. variable_permutation is a permutation of
    [vars(cnf)]. All the literals with the old i-th variable are
    replaced with the new i-th variable.

    3. Clause permutations. clause_permutation is a permutation of
    [0..m-1]. The resulting clauses are reordered according to the
    permutation.
"""

    # empty cnf
    out=CNF(header='')

    out.header="Reshuffling of:\n\n"+cnf.header


    vars=list(cnf.variables())
    N=len(vars)
    M=len(cnf)

    # variable permutation
    if variable_permutation==None:
        variable_permutation=vars
        random.shuffle(variable_permutation)
    else:
        assert len(variable_permutation)==N

    # polarity flip
    if polarity_flip==None:
        polarity_flip = [random.choice([-1,1]) for x in xrange(N)]
    else:
        assert len(polarity_flip)==N

    #
    # substitution of variables
    #
    for v in variable_permutation:
        out.add_variable(v)

    substitution=[None]*(2*N+1)
    reverse_idx=dict([(v,i) for (i,v) in enumerate(out.variables(),1)])
    polarity_flip = [None]+polarity_flip

    for i,v in enumerate(cnf.variables(),1):
        substitution[i]=  polarity_flip[i]*reverse_idx[v]
        substitution[-i]= -substitution[i]

    #
    # permutation of clauses
    #
    if clause_permutation==None:
        clause_permutation=range(M)
        random.shuffle(clause_permutation)

    # load clauses
    out._clauses = [None]*M
    for (old,new) in enumerate(clause_permutation):
        out._clauses[new]=tuple( substitution[l] for l in cnf._clauses[old])

    # load comments
    assert len(out._comments)==0
    clause_permutation.append((M,M)) # comments after last clause do not move
    for (pos,text) in cnf._comments:
        out._comments.append((clause_permutation[pos],text))
    clause_permutation.pop()
    def key(t): return t[0]
    out._comments.sort(key=key)


    # return the formula
    assert out._check_coherence(force=True)
    return out


def stableshuffle(inputfile,
                  outputfile,
                  variable_permutation=None,
                  clause_permutation=None,
                  polarity_flip=None):

    subst= None
    line_counter = 0
    header_buffer=["c Reshuffling of:\nc\n"]
    clause_counter = 0

    for l in inputfile.readlines():

        line_counter+=1

        # add the comment to the header (discard if it is in the middle)
        if l[0]=='c':
            if not subst: header_buffer.append(l)
            continue
    
        # parse spec line
        if l[0]=='p':
            if subst:
                raise ValueError("Syntax error: "+
                                 "line {} contains a second spec line.".format(line_counter))
            _,_,nstr,mstr = l.split()
            n = int(nstr)
            subst = substitution(n, variable_permutation, polarity_flip)
            m = int(mstr)

            # Clause permutation
            if clause_permutation==None:
                clause_permutation=range(m)
                random.shuffle(clause_permutation)
            
            clause_buffer=[None]*m

            # Print header
            for h in header_buffer:
                print(h,end='',file=outputfile)
            
            print(l,end='',file=outputfile)
            
            continue

        # parse literals
        clause = [int(lit) for lit in l.split()]

        # Checks at the end of clause
        if clause[-1] != 0:
            raise ValueError("Syntax error: last clause was incomplete")

        clause_buffer[clause_permutation[clause_counter]] = \
            " ".join([str(subst[i]) for i in clause])
        clause_counter += 1

    # Alternative algorithm that uses less memory:
    #    1. record positions of lines.
    #    2. for each (ordered) line in output, seek input, parse, substitute, write.
    for clause in clause_buffer :
        print(clause,file=outputfile)


def substitution(n, variable_permutation = None,
                 polarity_flip = None) :
    if variable_permutation is None :
        variable_permutation = range(1,n+1)
        random.shuffle(variable_permutation)
    else:
        assert len(variable_permutation)==n

    vars = [0] + variable_permutation

    if polarity_flip is None :
        polarity_flip = [random.choice([-1,1]) for x in xrange(n)]
    else:
        assert len(polarity_flip)==n

    flip = [0] + polarity_flip

    subst=[None]*(2*n+1)
    for i,p in enumerate(vars):
        subst[p]=i*flip[p]
    for i in xrange(1,n+1):
        subst[-i]= -subst[i]

    return subst


def command_line_reshuffle(argv):

    # Python 2.6 does not have argparse library
    try:
        import argparse
    except ImportError:
        print("Sorry: %s requires `argparse` library, which is missing.\n"%argv[0],file=sys.stderr)
        print("Either use Python 2.7 or install it from one of the following URLs:",file=sys.stderr)
        print(" * http://pypi.python.org/pypi/argparse",file=sys.stderr)
        print(" * http://code.google.com/p/argparse",file=sys.stderr)
        print("",file=sys.stderr)
        exit(-1)

    # Parse the command line arguments
    parser=argparse.ArgumentParser(prog='shuffle',epilog="""
    For more information type 'shuffle <formula type> [--help | -h ]'
    """)

    parser.add_argument('--output','-o',
                        type=argparse.FileType('wb',0),
                        metavar="<output>",
                        default='-',
                        help="""Output file. The formula is saved
                        on file instead of being sent to standard
                        output. Setting '<output>' to '-' is another
                        way to send the formula to standard output.
                        (default: -)
                        """)
    parser.add_argument('--seed','-S',
                        metavar="<seed>",
                        default=None,
                        type=str,
                        action='store',
                        help="""Seed for any random process in the
                        program. Any python hashable object will
                        be fine.  (default: current time)
                        """)
    parser.add_argument('--input','-i',
                        type=argparse.FileType('r',0),
                        metavar="<input>",
                        default='-',
                        help="""Input file. A formula in dimacs format. Setting '<input>' to '-' is
                        another way to read from standard input.
                        (default: -)
                        """)

    g=parser.add_mutually_exclusive_group()
    g.add_argument('--verbose', '-v',action='count',default=1,
                   help="""Include comments inside the formula. It may
                   not be supported by very old sat solvers.
                   """)
    g.add_argument('--quiet', '-q',action='store_const',const=0,dest='verbose',
                   help="""Output just the formula with not header
                   or comment.""")


    # Process the options
    args=parser.parse_args(argv[1:])

    # If necessary, init the random generator
    if hasattr(args,'seed') and args.seed:
        random.seed(args.seed)

    stableshuffle(args.input,args.output)

    if args.output!=sys.stdout:
        args.output.close()


### Launcher
if __name__ == '__main__':
    command_line_reshuffle(sys.argv)
