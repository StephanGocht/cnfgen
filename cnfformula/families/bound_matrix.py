from cnfformula.cnf import CNF

from cnfformula.cmdline import BipartiteGraphHelper

from cnfformula.graphs import bipartite_sets,enumerate_edges,neighbors

import cnfformula.families
import cnfformula.cmdline

import cnfformula.encoding.constructs as fe

import random
import itertools

from math import ceil,floor

from inspect import getdoc

@cnfformula.families.register_cnf_generator
def boundMatrix(*args, **kwargs):
    f = BoundMatrix(*args, **kwargs)
    return f.getFormula()

class BoundMatrix:
    r"""
    :param a: A :math:`m \times n` matrix A
    :param r: A vector of dimension :math:`m` providing the bounds for each row
    :param c: A vector of dimension :math:`n` providing the bounds for each column

    Create the formula of the form:

    ..math::
        \sum_{j \in [n]} a_{i,j} x_{i,j} \geq r_i
        \sum_{i \in [m]} a_{i,j} x_{i,j} \leq c_j
    """
    def __init__(self, a, r, c):
        self.a = a
        self.numRows = len(self.a)
        self.numCols = len(self.a[0])
        for i in range(self.numRows):
            if len(self.a[i]) != self.numCols:
                raise TypeError("Requireing a matrix that allows accessing by a[i][j] that has equal dimension in every row.")
            for j in range(self.numCols):
                try:
                    if not isinstance(a[i][j], int):
                        raise TypeError("Requireing integer matrix.")
                except LookupError:
                    raise TypeError("Requireing a matrix that allows accessing by a[i][j] that has equal dimension in every row.")

        self.r = r
        for i in range(self.numRows):
            try:
                if not isinstance(r[i], int):
                    raise TypeError("Requireing integer matrix.")
            except LookupError:
                raise TypeError("Requireing a matrix that allows accessing by a[i][j] that has equal dimension in every row.")

        self.c = c
        for j in range(self.numCols):
            try:
                if not isinstance(c[j], int):
                    raise TypeError("Requireing integer matrix.")
            except LookupError:
                raise TypeError("Requireing a matrix that allows accessing by a[i][j] that has equal dimension in every row.")


    def getFormula(self):
        self.f = CNF()
        self.addAllVariables()

        result = fe.And()
        for i in range(self.numRows):
            result.append(self.addRowConstraint(i))

        for j in range(self.numCols):
            result.append(self.addColConstraint(j))

        fe.toCNFgen(self.f,result)
        return self.f

    def addRowConstraint(self, i):
        return fe.GEQ([(self.a[i][j], self.x(i,j)) for j in range(self.numCols)], self.r[i])

    def addColConstraint(self, j):
        return fe.LEQ([(self.a[i][j], self.x(i,j)) for i in range(self.numRows)], self.c[j])

    def addVariable(self, var):
        self.f.add_variable(var)

    def addAllVariables(self):
        for i in range(self.numRows):
            for j in range(self.numCols):
                self.addVariable(self.x(i,j))

    def x(self, i, j):
        return "x_{%i,%i}" % (i,j)

@cnfformula.families.register_cnf_generator
def boundMatrixWithSplitConstraint(*args, **kwargs):
    f = BoundMatrixWithSplitConstraint(*args, **kwargs)
    return f.getFormula()

class BoundMatrixWithSplitConstraint(BoundMatrix):
    r"""
    :param a: A :math:`m \times n` matrix A
    :param r: A vector of dimension :math:`m` providing the bounds for each row
    :param c: A vector of dimension :math:`n` providing the bounds for each column

    Furthermore let :math:`T_i = \{j | a_{i,j} \neq 1\}` and let :math:`F_i,S_i`
    be the partition of :math:`\{j | a_{i,j} = 1\}` where :math:`F_i` contains
    the first half of the indices and :math:`S_i` the second half.

    For each row with :math:`|T_i| > 0` we encode:

    ..math::
        r_i      h_i  + \sum_{j \in T_i} a_{i,j} x_{i,j} + \sum_{j \in F_i} a_{i,j} x_{i,j} \geq r_i
        r_i \bar{h_i} + \sum_{j \in T_i} a_{i,j} x_{i,j} + \sum_{j \in S_i} a_{i,j} x_{i,j} \geq r_i
        \sum_{i \in [m]} a_{i,j} x_{i,j} \leq c_j

    Where :math:`h_i` is a fresh variable. For all other rows and
    columns the same constraitns as in BoundMatrix are used.
    """
    def h(self, i):
        return "h_{%i}" % (i)

    def addAllVariables(self):
        super().addAllVariables()
        for i in range(self.numRows):
            self.addVariable(self.h(i))

    def addRowConstraint(self, i):
        T = [j for j in range(self.numCols) if self.a[i][j] != 1]
        if len(T) == 0:
            return super().addRowConstraint(i)
        R = [j for j in range(self.numCols) if self.a[i][j] == 1]
        middle = len(R) // 2
        F = R[:middle]
        S = R[middle:]

        result = fe.And()
        result.append(
            fe.GEQ([(self.r[i], self.h(i))] +
            [(self.a[i][j], self.x(i,j)) for j in T] +
            [(self.a[i][j], self.x(i,j)) for j in F], self.r[i]))

        result.append(
            fe.GEQ([(self.r[i], fe.Not(self.h(i)))] +
            [(self.a[i][j], self.x(i,j)) for j in T] +
            [(self.a[i][j], self.x(i,j)) for j in S], self.r[i]))

        return result

@cnfformula.cmdline.register_cnfgen_subcommand
class SCCmdHelper(object):
    name='bound_matrix_strong_diagonal'
    description='LEQ column constraints and GEQ row constraints'

    @staticmethod
    def setup_command_line(parser):
        parser.description = r"""Create constraints: \sum_{j \in [n]} a_{i,j} x_{i,j}
        \geq r_i and \sum_{i \in [m]} a_{i,j} x_{i,j} \leq c_j. a_{i,j} = r_i if i = j
        otherwise 1."""

        parser.add_argument('--numRows','-m',type=int,
                            help="number of rows")
        parser.add_argument('--numCols','-n',type=int,
                            help="number of columns")
        parser.add_argument('--rowBound','-r',type=int,
                            help="bound for every row constraint (greater or equal)")
        parser.add_argument('--colBound','-c',type=int,
                            help="bound for every column constraint (less or equal)")

        parser.add_argument('--addOne','-a',default=False,action='store_true',
                    help="add one to the rhs of a random row constraint")
        parser.add_argument('--lastRowOne','-l',default=False,action='store_true',
                    help="set the rhs of the last row to one")

        parser.add_argument('--splitRows','-s',default=False,action='store_true',
                    help="split the row constrains in two halfs with helper variable")

    @staticmethod
    def build_cnf(args):
        a = [[1 if i != j else args.rowBound for j in range(args.numCols)] for i in range(args.numRows)]
        r = [args.rowBound] * args.numRows
        c = [args.colBound] * args.numCols
        if args.lastRowOne:
            r[-1] = 1

        if args.addOne:
            u = random.choice(range(args.numRows))
            r[u] += 1

        if args.splitRows:
            return boundMatrixWithSplitConstraint(a,r,c)
        else:
            return boundMatrix(a,r,c)