import random
import cnfformula.cmdline
import cnfformula.families
import math
from cnfformula.cnf import CNF

def toArgs(listOfTuples, operator, degree):
    return list(sum(listOfTuples, ())) + [operator, degree]


@cnfformula.families.register_cnf_generator
def xorCard(*args, **kwargs):
    xor_card = XorCard(*args, **kwargs)
    return xor_card()

class XorCard():
    """ Formula encoding Ax = b mod 2 and 1^Tx >= k for random A in R^mxn,b^m

    Personal Note: according to Kuldeep Meel these have various interesting
    applications for this kind of benchmarks. There will be a
    publication in SAT 2019 about this kind of formula.
    """

    def __init__(self, m, n, k, eq, encoding):
        self.m = m
        self.n = n
        self.k = k
        self.eq = eq
        self.encoding = encoding
        self.numXor = 0

    def x(self, i):
        return "x_%i"%(i)

    def h(self, i,j):
        return "h_(%i,%i)"%(i,j)

    def addXor(self, terms, value):
        w = len(terms)
        k = w // 2

        if k > 0:
            if self.encoding == "extendedPBAnyHelper":
                for i in range(k):
                    helper = ("xor_helper", i, self.numXor)
                    self.f.add_variable(helper)
                    terms.append((2, helper))
            elif self.encoding == "extendedPBOneHelper":
                helpers = list()
                for i in range(k):
                    helper = ("xor_helper", i, self.numXor)
                    helpers.append(helper)
                    self.f.add_variable(helper)
                    terms.append(((i+1)*2, helper))
                self.f.add_linear(*toArgs([(1, x) for x in helpers], "<=", 1))
            elif self.encoding == "extendedPBExpHelper":
                for i in range(math.ceil(math.log(k, 2)) + 1):
                    helper = ("xor_helper", i, self.numXor)
                    self.f.add_variable(helper)
                    terms.append((2**i * 2, helper))
            else:
                raise ValueError("Invalid encoding '%s'" % encoding)

        degree = 2 * k + (value % 2)
        self.f.add_linear(*toArgs(terms, "==", degree))
        self.numXor += 1

    def __call__(self):
        mn = self.m * self.n
        A = [0, 1] * (mn // 2) + [0] * (mn % 2)
        random.shuffle(A)
        A = [[A[i * self.n + j] for j in range(self.n)] for i in range(self.m)]
        b = [0, 1] * (self.m // 2) + [0] * (self.m % 2)


        self.f = CNF()

        terms = [(-1, self.x(i)) for i in range(self.n)]
        if self.eq:
            self.f.add_linear(*toArgs(terms, "==", -self.k))
        else:
            self.f.add_linear(*toArgs(terms, ">=", -self.k))

        for i in range(self.m):
            terms = [(1, self.x(j)) for j in range(self.n) if A[i][j] == 1]
            if len(terms) > 0:
                self.addXor(terms, b[i])

        return self.f


@cnfformula.cmdline.register_cnfgen_subcommand
class XorCardHelper(object):
    """ See XorCard
    """
    name = 'xor_card'
    description = 'xor cardinality formula'

    @staticmethod
    def setup_command_line(parser):
        """
        Arguments:
        - `parser`: parser to load with options.
        """
        parser.add_argument('-m', type=int)
        parser.add_argument('-n', type=int)
        parser.add_argument('-k', type=int)
        parser.add_argument('--eq', action='store_true', default=False)
        group = parser.add_mutually_exclusive_group()
        group.add_argument("--extendedPBAnyHelper", action='store_true',
                           help="Encode xor as pseudo boolean constraint with extended variables.")
        group.add_argument("--extendedPBOneHelper", action='store_true',
                           help="""Encode xor as pseudo boolean constraint with extended
                variables, such that exactly one of the extension variables ist
                true.""")
        group.add_argument("--extendedPBExpHelper", action='store_true',
                           help="""Encode xor as pseudo boolean constraint with extended
                variables, using powers of two encoding.""")

    @staticmethod
    def build_cnf(args):
        encoding = "extendedPBExpHelper"
        if args.extendedPBAnyHelper:
            encoding = "extendedPBAnyHelper"
        elif args.extendedPBOneHelper:
            encoding = "extendedPBOneHelper"
        elif args.extendedPBExpHelper:
            encoding = "extendedPBExpHelper"

        return xorCard(args.m, args.n, args.k, args.eq, encoding)
