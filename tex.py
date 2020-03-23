import argparse
import itertools
import os
import time
import sys
from virtual import VirtualInvolution, VirtualPermutation

if sys.version_info < (3, 0):
    major, minor = sys.version_info.major, sys.version_info.minor
    sys.stdout.write("\nSorry, requires Python 3. ")
    sys.stdout.write("(This is Python %s.%s.)\n\n" % (major, minor))
    sys.exit(1)


class TexMixin:

    """
    Mixin class with some helper functions for string formatting.
    """

    def write(self, force):
        self._tex()
        if not force and os.path.isfile(self.path):
            print ("* Aborting: file `%s` exists. Delete this or use `-f` flag to regenerate." % self.path)
            return False
        with open(self.path, 'w') as f:
            f.write('\n'.join(self.lines))
        return True

    def tex_char(self, ch):
        y, i, j = self.y, self.i, self.j

        if ch == i:
            return 'i'
        if ch == j:
            return 'j'
        if ch == y(i):
            return 'y_i'
        if ch == y(j):
            return 'y_j'

        if ch == -i:
            return "i'"
        if ch == -j:
            return "j'"
        if ch == -y(i):
            return "y_{i'}"
        if ch == -y(j):
            return "y_{j'}"

        p, q = VirtualPermutation.CYCLE_CHARS
        if ch == p:
            return 'P'
        if ch == q:
            return 'Q'

        r = VirtualPermutation.FIXED_CHAR
        if ch == r:
            return 'R'

    def tex_list(self, pi):
        tup = tuple(self.tex_char(c) for c in pi)
        return '\\dash '.join(('',) + tup + ('',))

    def tex_order(self):
        y, i, j = self.y, self.i, self.j

        order = []
        for a in range(1, 1 + y.rank):
            if a == i == y(i):
                order.append('y_i = i')
            elif a == j == y(j):
                order.append('j = y_j')
            else:
                order.append(self.tex_char(a))
        return ' < '.join(order)

    def tex_cycles(self, z):
        y, i, j = self.y, self.i, self.j

        k, l = y(i), y(j)
        cyc = {tuple(sorted([a, z(a)])) for a in (i, j, k, l)}
        pos_cyc = ['(%s,%s)' % (self.tex_char(a), self.tex_char(b)) for a, b in cyc]
        neg_cyc = ['(%s,%s)' % (self.tex_char(-a), self.tex_char(-b)) for a, b in cyc]
        return '\\{%s\\}' % ','.join(pos_cyc), '\\{%s\\}' % ','.join(neg_cyc)

    def _tex_properties(self, order, tuples, letter='Z'):
        def ch(a):
            return self.tex_char(a)

        prop1 = sorted({
            "$(wt)^{-1} = \\dash %s \\dash %s \\dash$" % (ch(b), ch(a))
            for a, b, c, d in tuples if order[a] < order[b]
        } | {
            "$(wt)^{-1} = \\dash %s \\dash %s \\dash$" % (ch(d), ch(c))
            for a, b, c, d in tuples if order[c] < order[d]
        })
        prop2 = sorted({
            "$(wt)^{-1} \\neq \\dash %s \\dash %s \\dash %s \\dash$ and $(wt)^{-1}\\neq \\dash %s \\dash %s \\dash %s \\dash$"
            % (ch(b), ch(c), ch(a), ch(b), ch(d), ch(a))
            for a, b, c, d in tuples if order[a] < order[c] < order[d] < order[b]
        } | {
            "$(wt)^{-1} \\neq \\dash %s \\dash %s \\dash %s \\dash$" % (ch(b), ch(c), ch(a))
            for a, b, c, d in tuples if order[a] < order[c] == order[d] < order[b]
        })
        prop3 = sorted({
            "$(wt)^{-1} = \\dash %s \\dash %s \\dash$" % (ch(a), ch(d))
            for a, b, c, d in tuples if order[a] < order[c] and order[b] < order[d]
        })

        def j(v):
            if len(v) == 0:
                return '(no condition).'
            if len(' and '.join(v).split('and')) > 2:
                par = ['\\text{' + c + '}' for c in v]
                return '$\\begin{cases}' + '\\text{ and }\\\\\n'.join(par) + '.\\end{cases}$'
            else:
                return '  and '.join(v) + '.'

        self.lines += ['\\begin{enumerate}']
        self.lines += ['\\item[](%s1) $\\Leftrightarrow$ ' % letter + j(prop1)]
        self.lines += ['\\item[](%s2) $\\Leftrightarrow$ ' % letter + j(prop2)]
        self.lines += ['\\item[](%s3) $\\Leftrightarrow$ ' % letter + j(prop3)]
        self.lines += ['\\end{enumerate}']

    def _tex_process_reasons(self, reasons):
        mapping = {
            VirtualInvolution.REASON_B1: '(T)',
            VirtualInvolution.REASON_B2: '(U)',
            VirtualInvolution.REASON_F1: '(Y3)',
            VirtualInvolution.REASON_F2: '(Y2)',
            VirtualInvolution.REASON_F3: '(Y3)',
            VirtualInvolution.REASON_F4: '(Y3)',
            VirtualInvolution.REASON_C1: '(Y1)',
            VirtualInvolution.REASON_C2: '(Y3)',
            VirtualInvolution.REASON_C3: '(Y2)',
            VirtualInvolution.REASON_C4: '(Y2)',
        }
        reason, data = reasons[0]
        if reason not in [VirtualInvolution.REASON_B1, VirtualInvolution.REASON_B2]:
            if reason == VirtualInvolution.REASON_C1:
                a, b = data
                a, b = self.tex_char(a), self.tex_char(b)
                return mapping[reason] + ' fails for $(a,b)=(%s,%s)$' % (a, b)
            else:
                a, b, c, d = data
                a, b, c, d = self.tex_char(a), self.tex_char(b), self.tex_char(c), self.tex_char(d)
                return mapping[reason] + ' fails for $(a,b)=(%s,%s)$ and $(a\',b\')=(%s,%s)$' % (a, b, c, d)
        else:
            return mapping[reason] + ' fails'


class CoveringPropertyTexWriter(TexMixin):

    def __init__(self, path=None):
        directory = os.path.dirname(os.path.abspath(__file__))
        self.path = path if path else os.path.join(directory, 'tex/covering-property.tex')
        self.lines = None
        self.y = None
        self.i = None
        self.j = None

    def _tex(self):
        self.lines = ["""
\\documentclass[10pt]{article}
\\usepackage{amsmath,amssymb,amsthm,fullpage,hyperref}
\\usepackage[margin=0.75in]{geometry}
\\usepackage[shortlabels]{enumitem}

\\theoremstyle{definition}
\\newtheorem*{theorem}{Theorem}
\\theoremstyle{definition}
\\newtheorem{lemma}{Lemma}

\\def\\dash{\\text{\\hspace{0.5mm}---\\hspace{0.5mm}}}
\\def\\Fix{\\mathrm{Fix}}
\\def\\Cyc{\\mathrm{Cyc}}
\\def\\ZZ{\\mathbb{Z}}

\\begin{document}

\\title{Computer-generated proof of affine involution covering property}
\\author{Eric MARBERG \\and Yifeng ZHANG}
\\maketitle
\\tableofcontents

\\section{Setup}

Let $n$ be a positive integer.
For the definition of the affine symmetric group $\\tilde S_n$, see \\cite{M}.
Fix an affine permutation $w \\in \\tilde S_n$ and an involution $y =y^{-1} \\in\\tilde S_n$.
We set $y_a = y(a)$ for $a \\in \\ZZ$ and define
\\[\\Cyc(y) = \\{ (a,b) \\in \\ZZ\\times\\ZZ : a \\leq b = y_a\\}.\\]
As a shorthand, we write $w^{-1} = \\dash a\\dash b\\dash c \\dash \\cdots\\dash d \\dash$
to mean that $w_a < w_b < w_c < \\dots < w_d$.

\\begin{lemma}\\label{lem-1}
One has $w \\in \\mathcal{A}(y)$
if and only if for all $(a,b),(a',b') \\in \\Cyc(y)$, the following properties hold:
\\begin{enumerate}
\\item[(Y1)] If $a < b$ then $w^{-1} = \\dash b \\dash a \\dash$.
\\item[(Y2)] If $a < a' \\leq b' < b$ then $w^{-1} \\neq \\dash b \\dash a' \\dash a \\dash$
and $w^{-1}\\neq \\dash b \\dash b' \\dash a \\dash.$
\\item[(Y3)] If $a < a'$ and $b < b'$ then $w^{-1} = \\dash a \\dash b' \\dash.$
\\end{enumerate}
\\end{lemma}

\\begin{proof}
This is equivalent to \\cite[Theorem 7.6]{M}.
\\end{proof}

Fix integers $i < j$ that are not congruent modulo $n$.
Let $t=t_{ij} \\in \\tilde S_n$ denote the reflection
that interchanges $i$ and $j$ while fixing all integers not congruent to
$i$ or $j$ modulo $n$.
Write $\\lessdot$ for the covering relation in the Bruhat order on $\\tilde S_n$.

\\begin{lemma}
One has $w \\lessdot wt$
if and only if the following property holds:
\\begin{enumerate}
\\item[(T)] $w^{-1} = \\dash i \\dash j \\dash$ but if $i<e<j$
then $w^{-1} \\neq \\dash i \\dash e \\dash j\\dash$.
\\end{enumerate}
Moreover, if $i\'$ and $j\'$ are integers with $i-i\' = j-j\' \\in n\\ZZ$,
then property (T) is equivalent to the following:
\\begin{enumerate}
\\item[(U)] $w^{-1} = \\dash i\' \\dash j\' \\dash$ but if $i\'<e<j\'$
then $w^{-1} \\neq \\dash i\' \\dash e \\dash j\'\\dash$.
\\end{enumerate}
\\end{lemma}

\\begin{proof}
This is equivalent to \\cite[Proposition 8.3.6]{BB}.
\\end{proof}

Recall the definition of the operator $\\tau^n_{ij}$ from \\cite[\\S8]{M} and
let $z = z^{-1} = \\tau^n_{ij}(y) \\in \\tilde S_n$.

\\begin{theorem}
Assume $\\{i, y_i\\} + n \\ZZ$ and $\\{j,y_j\\} + n \\ZZ$ are disjoint.
If $y \\neq z$, $w \\in \\mathcal{A}(y)$, and $w\\lessdot wt$, then $wt \\in \\mathcal{A}(z)$.
\\end{theorem}

The proof of this statement occupies the rest of this computer-generated document.
\\begin{proof}
Assume that  $\\{i, y_i\\} + n \\ZZ$ and $\\{j,y_j\\} + n \\ZZ$ are disjoint
and that $y \\neq z$ and $w \\in \\mathcal{A}(y)$ and $w\\lessdot wt$.
Observe that if $i \\neq y_i$ then the sets $i + n\\ZZ$ and $y_i + n \\ZZ$ are disjoint,
and that if $j \\neq y_j$ then the sets $j + n\\ZZ$ and $y_j + n\\ZZ$ are disjoint.

To show that $wt \\in \\mathcal{A}(z)$, it suffices by Lemma~\\ref{lem-1} to check that if
$(a,b),(a',b') \\in \\Cyc(z)$ then the following properties hold:
\\begin{enumerate}
\\item[(Z1)] If $a < b$ then $(wt)^{-1} = \\dash b \\dash a \\dash$.
\\item[(Z2)] If $a < a' \\leq b' < b$ then $(wt)^{-1} \\neq \\dash b \\dash a' \\dash a \\dash$
and $(wt)^{-1}\\neq \\dash b \\dash b' \\dash a.$
\\item[(Z3)] If $a < a'$ and $b < b'$ then $(wt)^{-1} = \\dash a \\dash b' \\dash.$
\\end{enumerate}
Let $E = \\{i, j, y_i, y_j\\}$.
Then $w_a = (wt)_a$ and $y_a = z_a$ for all integers $a \\notin E + n\\ZZ$,
and we may decompose $\\Cyc(z)$ as a disjoint union of four subsets
$
\\Cyc(z) = \\Cyc^1(z) \\sqcup \\Cyc^2(z) \\sqcup \\Cyc^3(z)
$
where
\\[
\\begin{aligned}
\\Cyc^1(z) &= \\{ (a,b) \\in \\Cyc(z): a,b \\in E\\},\\\\
\\Cyc^2(z) &= \\{ (a,b) \\in \\Cyc(y): a,b \\notin E + n\\ZZ\\} =
              \\{ (a,b) \\in \\Cyc(z): a,b \\notin E + n\\ZZ\\},\\\\
\\Cyc^3(z) &= \\{ (a+mn,b+mn): 0 \\neq m \\in \\ZZ\\text{ and }(a,b)\\in \\Cyc^1(z)\\}.
\\end{aligned}
\\]
When $(a,b),(a',b') \\in \\Cyc^2(z)\\subset \\Cyc(y)$,
properties (Z1)-(Z3) are equivalent to (Y1)-(Y3)
and therefore hold since $w \\in \\mathcal{A}(y)$.
It remains to check properties (Z1)-(Z3) in the following cases:
\\begin{itemize}
\\item[(i)] When $(a,b),(a',b') \\in \\Cyc^1(z)$.
\\item[(ii)] When one of the pairs $(a,b)$, $(a',b')$ belongs to $\\Cyc^1(z)$
             while the other belongs to $\\Cyc^2(z)$.
\\item[(iii)] When $(a,b) \\in \\Cyc^1(z)$ and $(a',b') \\in \\Cyc^3(z)$,
              or $(a',b') \\in \\Cyc^1(z)$ and $(a,b) \\in \\Cyc^3(z)$.
\\end{itemize}
Since we assume $z = \\tau^n_{ij}(y) \\neq y$,
there are twelve possibilities for the relative orders of $i$, $j$, $y_i$, and $y_j$.
We examine each of these possibilities in turn and check directly that
properties (Z1)-(Z3) hold in cases (i), (ii), and (iii).
"""]

        for y in VirtualInvolution.all(maximum_size=4, mimimal_type=True):
            for i, j in itertools.combinations(range(1, y.rank + 1), 2):
                if y.tau(i, j) != y:
                    self.y = y
                    self.i = i
                    self.j = j
                    self._tex_involution_analysis()

        self.lines += ["""
\\section{Conclusion}
It follows from this exhaustive case analysis
that properties (Z1)-(Z3) hold for all pairs $(a,b),(a\',b\') \\in \\Cyc(z)$.
We conclude by Lemma~\\ref{lem-1} that $wt \\in \\mathcal{A}(z)$.
This completes the proof of the theorem.
\\end{proof}

\\begin{thebibliography}{99}

\\bibitem{BB} A. Bj\\"orner and F. Brenti,
\\emph{Combinatorics of Coxeter groups},
Graduate Texts in Mathematics 231, Springer, New York, 2005.

\\bibitem{M} E. Marberg,
On some actions of the $0$-Hecke monoids of affine symmetric groups,
\\emph{J. Combin. Theory Ser. A} \\textbf{161} (2019), 178--219.

\\end{thebibliography}

\\end{document}
"""]

    def _tex_involution_analysis(self):
        self.lines += ['\\section{Case: $%s$}' % self.tex_order()]
        self.lines += ['Suppose $y$ is such that $%s$.' % self.tex_order()]

        z = self.y.tau(self.i, self.j)
        z_cyc, neg_z_cyc = self.tex_cycles(z)
        self.lines += ['Then $z = \\tau^n_{ij}(y)$ has $\\Cyc^1(z) = %s.$' % z_cyc]

        self.lines += ['\\subsection{Subcase (i)}']
        base = tuple(sorted(self.y.involution))
        valid, invalid = [], []
        for pi in itertools.permutations(base):
            errors = self._tex_invalid_atom_analysis(base, pi)
            if errors:
                invalid += errors
            else:
                valid += [pi]

        invalid = [line for line, _ in sorted(invalid, key=lambda pair: pair[1])]
        assert len(valid) == 1
        pi = valid[0]

        self.lines += ['We must have $w^{-1} = %s$' % self.tex_list(pi)]
        self.lines += ['since no other ordering is possible:']
        self.lines += ['\\begin{enumerate}'] + invalid + ['\\end{enumerate}']

        all_mirror, all_double, all_single = VirtualPermutation.maximal_extensions(pi)
        virtual = VirtualPermutation(pi, all_mirror, all_double, all_single)
        required_ascents = {(self.i, self.j)}
        invalid_dictionary = self.y.get_invalid_configurations(virtual, required_ascents)
        mirror = {e: all_mirror[e] - set(invalid_dictionary[e].keys()) for e in all_mirror}
        double = {e: all_double[e] - set(invalid_dictionary[e].keys()) for e in all_double}
        single = {e: all_single[e] - set(invalid_dictionary[e].keys()) for e in all_single}

        w = VirtualPermutation(pi, mirror, double, single)
        wt = w.transpose(self.i, self.j)
        assert z.is_virtual_atom(wt)

        self.lines += ['Hence if $%s$ then \\begin{enumerate}\\item[] $(wt)^{-1} = %s$. \\end{enumerate}' % (self.tex_order(), self.tex_list(wt.permutation))]
        self.lines += ['When $(a,b),(a\',b\')\\in\\Cyc^1(z)= %s$,' % z_cyc]
        self.lines += ['properties (Z1)-(Z3) are equivalent to the following conditions which all hold in this case:']

        order = {b: i for i, b in enumerate(base)}
        cyc = {(i, z(i)) for i in range(1, z.rank + 1) if i <= z(i)}
        tuples = [(a, b, c, d) for a, b in cyc for c, d in cyc]
        self._tex_properties(order, tuples)
        self.lines += ['Thus properties (Z1)-(Z3) hold whenever $(a,b)$, $(a\',b\')$ are as in case (i) and $%s$.' % self.tex_order()]

        y, i, j = self.y, self.i, self.j
        subset = '\\{i,j' + (',y_i' if y(i) != i else '') + (',y_j' if y(j) != j else '') + '\\}'

        c = self.tex_char(VirtualPermutation.FIXED_CHAR)
        self.lines += ['\\subsection{Subcase (ii)}']
        self.lines += ['Suppose $%s$ is an integer such that $(%s,%s) \\in \\Cyc^2(z)\\subset\\Cyc(y)$, so that ' % (c, c, c)]
        self.lines += ['$%s = y_%s = z_%s \\notin %s + n\\mathbb{Z}$.' % (c, c, c, subset)]
        self._tex_list_extensions_single(w, invalid_dictionary, all_single)

        p, q = VirtualPermutation.CYCLE_CHARS
        p, q = self.tex_char(p), self.tex_char(q)
        self.lines += ['Next suppose $%s < %s$ are integers with $(%s, %s) \\in \\Cyc^2(z)\\subset\\Cyc(y)$, so that ' % (p, q, p, q)]
        self.lines += ['$%s = y_{%s} = z_{%s}$ and $%s,%s\\notin %s + n\\ZZ$.' % (q, p, p, p, q, subset)]
        self._tex_list_extensions_double(w, invalid_dictionary, all_double)
        self.lines += ['We conclude that properties (Z1)-(Z3) hold whenever $(a,b)$, $(a\',b\')$ are as in cases (i) or (ii) and $%s$.' % self.tex_order()]

        _i, _j = self.tex_char(-self.i), self.tex_char(-self.j)
        self.lines += ['\\subsection{Subcase (iii)}']
        self.lines += ['Suppose $%s$ and $%s$ are integers such that' % (_i, _j)]
        self.lines += ['$0\\neq i - %s = j - %s \\in n\\ZZ$,' % (_i, _j)]
        self.lines += ['so that $w(i) - w(%s) = w(j) - w(%s) = i - %s$.' % (_i, _j, _i)]
        self._tex_list_extensions_mirror(w, invalid_dictionary, all_mirror)
        self.lines += ['We conclude that properties (Z1)-(Z3) hold for all ']
        self.lines += ['$(a,b),(a\',b\') \\in \\Cyc(z)$ when $%s$.' % self.tex_order()]

    def _tex_invalid_atom_analysis(self, base, pi):
        virtual = VirtualPermutation(pi, {}, {}, {})
        invalid_dictionary = self.y.get_invalid_configurations(virtual, required_ascents={(self.i, self.j)})
        if invalid_dictionary:
            assert list(invalid_dictionary) == [base]
            assert pi in invalid_dictionary[base]
            reasons = invalid_dictionary[base][pi]
            prop = self._tex_process_reasons(reasons)
            return [('\\item If $w^{-1} = %s$ then %s.' % (self.tex_list(pi), prop), prop)]
        else:
            return []

    SINGLE = 0
    DOUBLE = 1
    MIRROR = 2

    def _tex_list_extensions_single(self, w, invalid_dict, all_dict):
        self._tex_list_extensions(w, invalid_dict, all_dict, w.single_extensions, self.SINGLE)

    def _tex_list_extensions_double(self, w, invalid_dict, all_dict):
        self._tex_list_extensions(w, invalid_dict, all_dict, w.double_extensions, self.DOUBLE)

    def _tex_list_extensions_mirror(self, w, invalid_dict, all_dict):
        self._tex_list_extensions(w, invalid_dict, all_dict, w.mirror_extensions, self.MIRROR)

    def _tex_list_extensions(self, w, invalid_dictionary, all_dict, valid_dict, option):
        start = [base for base in set(invalid_dictionary) & set(all_dict) if valid_dict[base]]
        end = [base for base in set(invalid_dictionary) & set(all_dict) if not valid_dict[base]]

        self.lines += ['\\begin{enumerate}']
        for index, base in enumerate(start + end):
            order = ' < '.join(self.tex_char(a) for a in base)
            item = '$%s$.' % (index + 1)

            if valid_dict[base]:
                self.lines += ['\\item[%s] Suppose $%s$.' % (item, order)]
            else:
                self.lines += ['\\item[%s] It cannot happen that $%s$ since:' % (item, order)]

            self.lines += ['\\begin{enumerate}[(a)]']
            items = {
                pi: self._tex_process_reasons(reasons)
                for pi, reasons in invalid_dictionary[base].items()
            }
            for pi, prop in sorted(items.items(), key=lambda pair: pair[1]):
                self.lines += ['\\item If $w^{-1} = %s$ then %s.' % (self.tex_list(pi), prop)]
            self.lines += ['\\end{enumerate}']

            if valid_dict[base]:
                self.lines += ['Thus if $%s$ then one of the following holds:' % order]
                self.lines += ['\\begin{enumerate}']
                for pi in valid_dict[base]:
                    i, j = self.i, self. j
                    t = {i: j, j: i, -i: -j, -j: -i}
                    sigma = tuple(t.get(x, x) for x in pi)

                    p, q = self.tex_list(pi), self.tex_list(sigma)
                    self.lines += ['\\item[$\\bullet$] $w^{-1} = %s$ and $(wt)^{-1} = %s$.' % (p, q)]
                self.lines += ['\\end{enumerate}']

                plural = len(valid_dict[base]) > 1
                self._tex_conclusions(base, plural, option)

        self.lines += ['\\end{enumerate}']

    def _tex_conclusions(self, base, plural, option):
        if option == self.SINGLE:
            self._tex_single_conclusions(base, plural)
        elif option == self.DOUBLE:
            self._tex_double_conclusions(base, plural)
        elif option == self.MIRROR:
            self._tex_mirror_conclusions(base, plural)
        else:
            raise NotImplementedError

    def _tex_single_conclusions(self, base, plural):
        z = self.y.tau(self.i, self.j)
        order = {b: i for i, b in enumerate(base)}
        cyc_a = {(VirtualPermutation.FIXED_CHAR, VirtualPermutation.FIXED_CHAR)}
        cyc_b = {(i, z(i)) for i in range(1, z.rank + 1) if order[i] <= order[z(i)]}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]
        tuples += [(c, d, a, b) for a, b in cyc_a for c, d in cyc_b]

        z_cyc, _ = self.tex_cycles(z)
        c = self.tex_char(VirtualPermutation.FIXED_CHAR)

        self.lines += ['When $(a,b)= (%s,%s)$ and $(a\',b\')\\in \\Cyc^1(z)=%s$ or vice versa,' % (c, c, z_cyc)]
        self.lines += ['properties (Z1)-(Z3) correspond to the following conditions which']
        self.lines += ['hold in each of the available cases for $wt$:']
        self._tex_properties(order, tuples)

    def _tex_double_conclusions(self, base, plural):
        z = self.y.tau(self.i, self.j)
        order = {b: i for i, b in enumerate(base)}
        cyc_a = {VirtualPermutation.CYCLE_CHARS}
        cyc_b = {(i, z(i)) for i in range(1, z.rank + 1) if order[i] <= order[z(i)]}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]
        tuples += [(c, d, a, b) for a, b in cyc_a for c, d in cyc_b]

        z_cyc, _ = self.tex_cycles(z)
        p, q = VirtualPermutation.CYCLE_CHARS
        p, q = self.tex_char(p), self.tex_char(q)

        self.lines += ['When $(a,b)= (%s,%s)$ and $(a\',b\')\\in \\Cyc^1(z)=%s$ or vice versa,' % (p, q, z_cyc)]
        self.lines += ['properties (Z1)-(Z3) correspond to the following conditions which']
        self.lines += ['hold in each of the available cases for $wt$:']
        self._tex_properties(order, tuples)

    def _tex_mirror_conclusions(self, base, plural):
        z = self.y.tau(self.i, self.j)
        order = {b: i for i, b in enumerate(base)}
        cyc_a = {(i, z(i)) for i in range(1, z.rank + 1) if i <= z(i)}
        cyc_b = {(-i, -z(i)) for i in range(1, z.rank + 1) if i <= z(i)}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]
        tuples += [(a, b, c, d) for a, b in cyc_b for c, d in cyc_a]

        z_cyc, neg_z_cyc = self.tex_cycles(z)

        self.lines += ['When $(a,b)\\in\\Cyc^1(z)=%s$ and $(a\',b\')\\in%s$,' % (z_cyc, neg_z_cyc)]
        self.lines += ['properties (Z1)-(Z3) correspond to the following conditions which']
        self.lines += ['hold in each of the available cases for $wt$:']
        self._tex_properties(order, tuples)


class TogglingPropertyTexWriter(TexMixin):

    def __init__(self, path=None):
        directory = os.path.dirname(os.path.abspath(__file__))
        self.path = path if path else os.path.join(directory, 'tex/toggling-property.tex')
        self.lines = None
        self.y = None
        self.i = None
        self.j = None
        self.w = None

    def _tex(self):
        self.lines = ["""
\\documentclass[10pt]{article}
\\usepackage{amsmath,amssymb,amsthm,fullpage,hyperref}
\\usepackage[margin=0.75in]{geometry}
\\usepackage[shortlabels]{enumitem}

\\theoremstyle{definition}
\\newtheorem*{theorem}{Theorem}
\\theoremstyle{definition}
\\newtheorem{lemma}{Lemma}

\\def\\dash{\\text{\\hspace{0.5mm}---\\hspace{0.5mm}}}
\\def\\Fix{\\mathrm{Fix}}
\\def\\Cyc{\\mathrm{Cyc}}
\\def\\ZZ{\\mathbb{Z}}
\\def\\cA{\\mathcal{A}}

\\begin{document}

\\title{Computer-generated proof of affine involution toggling property}
\\author{Eric MARBERG \\and Yifeng ZHANG}
\\maketitle
\\tableofcontents

\\section{Setup}

Let $n$ be a positive integer.
For the definition of the affine symmetric group $\\tilde S_n$, see \\cite{M}.
Fix an affine permutation $w \\in \\tilde S_n$ and an involution $y =y^{-1} \\in\\tilde S_n$.
We set $y_a = y(a)$ for $a \\in \\ZZ$ and define
\\[\\Cyc(y) = \\{ (a,b) \\in \\ZZ\\times\\ZZ : a \\leq b = y_a\\}.\\]
As a shorthand, we write $w^{-1} = \\dash a\\dash b\\dash c \\dash \\cdots\\dash d \\dash$
to mean that $w_a < w_b < w_c < \\dots < w_d$.

\\begin{lemma}\\label{lem-1}
One has $w \\in \\cA(y)$
if and only if for all $(a,b),(a',b') \\in \\Cyc(y)$, the following properties hold:
\\begin{enumerate}
\\item[(Y1)] If $a < b$ then $w^{-1} = \\dash b \\dash a \\dash$.
\\item[(Y2)] If $a < a' \\leq b' < b$ then $w^{-1} \\neq \\dash b \\dash a' \\dash a \\dash$
and $w^{-1}\\neq \\dash b \\dash b' \\dash a \\dash.$
\\item[(Y3)] If $a < a'$ and $b < b'$ then $w^{-1} = \\dash a \\dash b' \\dash.$
\\end{enumerate}
\\end{lemma}

\\begin{proof}
This is equivalent to \\cite[Theorem 7.6]{M}.
\\end{proof}

Fix integers $i < j$ that are not congruent modulo $n$.
Let $t_{ij} \\in \\tilde S_n$ be the reflection
that interchanges $i$ and $j$ while fixing all integers not congruent to
$i$ or $j$ modulo $n$.
Write $\\lessdot$ for the covering relation in the Bruhat order on $\\tilde S_n$.

\\begin{lemma}\\label{lem-2}
One has $w \\lessdot wt_{ij}$
if and only if the following property holds:
\\begin{enumerate}
\\item[(T)] $w^{-1} = \\dash i \\dash j \\dash$ but if $i<e<j$
then $w^{-1} \\neq \\dash i \\dash e \\dash j\\dash$.
\\end{enumerate}
Moreover, if $i'$ and $j'$ are integers with $i-i' = j-j' \\in n\\ZZ$,
then property (T) is equivalent to the following:
\\begin{enumerate}
\\item[(U)] $w^{-1} = \\dash i' \\dash j' \\dash$ but if $i'<e<j'$
then $w^{-1} \\neq \\dash i' \\dash e \\dash j'\\dash$.
\\end{enumerate}
\\end{lemma}

\\begin{proof}
This is equivalent to \\cite[Proposition 8.3.6]{BB}.
\\end{proof}

Recall the definition of the operator $\\tau^n_{ij}$ from \\cite[\\S8]{M} and
let $z = z^{-1} = \\tau^n_{ij}(y) \\in \\tilde S_n$.

\\begin{lemma}\\label{lem-3}
Suppose $w \\in \\cA(y)$ and $w \\lessdot wt_{ij}$ and $y = \\tau^n_{ij}(y)$.
Then one of the following cases occurs:
\\begin{enumerate}
\\item[(A1)] $i < j = y_j < y_i$ and $w^{-1} = \\dash y_i \\dash i \\dash j \\dash$.
\\item[(A2)] $i < j < y_j < y_i$ and $w^{-1} = \\dash y_j \\dash y_i \\dash i \\dash j \\dash$.
\\item[(A3)] $i < y_j < j < y_i$ and $w^{-1} = \\dash y_i \\dash i  \\dash j  \\dash y_j \\dash$.
\\item[(B1)] $y_j < i = y_i < j$ and $w^{-1} =  \\dash i \\dash j \\dash y_j \\dash$.
\\item[(B2)] $y_j < i < y_i < j$ and $w^{-1} = \\dash y_i \\dash i  \\dash j  \\dash y_j \\dash$.
\\item[(B3)] $y_j < y_i < i < j$ and $w^{-1} = \\dash  i \\dash j \\dash y_j \\dash y_i \\dash$.
\\item[(C1)] $i < j < y_j < y_i$ and $w^{-1} = \\dash y_i \\dash i \\dash y_j \\dash j \\dash$.
\\item[(C2)] $y_j < y_i < i < j$ and $w^{-1} = \\dash  i \\dash y_i  \\dash j  \\dash y_j  \\dash$.
\\end{enumerate}
\\end{lemma}

\\begin{proof}
By definition,
the only way one can have $y = \\tau^n_{ij}(y)$
outside the given cases is if
$y_j = i < j = y_i$ or $y_j < i < j < y_i$, but then
any element $w \\in \\cA(y)$ has
$w^{-1} = \\dash j \\dash i \\dash$ by Lemma~\\ref{lem-1}
so it cannot hold that $w\\lessdot wt_{ij}$.
When $y$ corresponds to the one of the given cases,
the possibilities for $w \\in \\cA(y)$ with $w\\lessdot wt_{ij}$
are completely determined by Lemmas~\\ref{lem-1} and \\ref{lem-2}.
\\end{proof}

\\begin{theorem}
Suppose $w \\in \\cA(y)$ and $w \\lessdot wt_{ij}$ and $y = \\tau^n_{ij}(y)$.
Define
\\[
k = \\begin{cases}
j &\\text{in cases (A1)-(A3)} \\\\
y_j &\\text{in cases (B1)-(B3) and (C1)-(C2)}
\\end{cases}
\\quad\\text{and}\\quad
l =  \\begin{cases}
y_i &\\text{in cases (A1)-(A3) and (C1)-(C2)} \\\\
i &\\text{in cases (B1)-(B3).}
\\end{cases}
\\]
Then $k<l \\notin k + n\\ZZ$ and $w \\neq w t_{ij} t_{kl} \\in \\cA(y)$.
\\end{theorem}

The proof of this statement occupies the rest of this computer-generated document.
\\begin{proof}
By hypothesis, we are in one of the eight cases in Lemma~\\ref{lem-3}.
The sets $\\{i,y_i\\} + n\\ZZ$ and $\\{j,y_j\\} + n \\ZZ$ are therefore disjoint.
Note that if $i \\neq y_i$ then the sets $i + n\\ZZ$ and $y_i + n \\ZZ$ are disjoint,
and that if $j \\neq y_j$ then the sets $j + n\\ZZ$ and $y_j + n\\ZZ$ are disjoint.

Let $v = wt_{ij}t_{kl}$.
To show that $v \\in \\cA(y)$, it suffices by Lemma~\\ref{lem-1}
to check that if $(a,b),(a',b') \\in \\Cyc(y)$ then the following properties hold:
\\begin{enumerate}
\\item[(V1)] If $a < b$ then $v^{-1} = \\dash b \\dash a \\dash$.
\\item[(V2)] If $a < a' \\leq b' < b$ then $v^{-1} \\neq \\dash b \\dash a' \\dash a \\dash$
and $v^{-1}\\neq \\dash b \\dash b' \\dash a \\dash.$
\\item[(V3)] If $a < a'$ and $b < b'$ then $v^{-1} = \\dash a \\dash b' \\dash.$
\\end{enumerate}
Let $E = \\{i, j, y_i, y_j\\}$.
Then $v_a = w_a$ for all integers $a \\notin E + n\\ZZ$,
and
$
\\Cyc(y) = \\Cyc^1(y) \\sqcup \\Cyc^2(y) \\sqcup \\Cyc^3(y)
$
where
\\[
\\begin{aligned}
\\Cyc^1(y) &= \\{ (a,b) \\in \\Cyc(y): a,b \\in E\\},\\\\
\\Cyc^2(y) &= \\{ (a,b) \\in \\Cyc(y): a,b \\notin E + n\\ZZ\\},\\\\
\\Cyc^3(y) &= \\{ (a+mn,b+mn): 0 \\neq m \\in \\ZZ\\text{ and }(a,b)\\in \\Cyc^1(y)\\}.
\\end{aligned}
\\]
When $(a,b),(a',b') \\in \\Cyc^2(y)$,
properties (V1)-(V3) are equivalent to (Y1)-(Y3)
and therefore hold since $w \\in \\cA(y)$.
It remains to check properties (V1)-(V3) in the following cases:
\\begin{itemize}
\\item[(i)] When $(a,b),(a',b') \\in \\Cyc^1(y)$.
\\item[(ii)] When one of the pairs $(a,b)$, $(a',b')$ belongs to $\\Cyc^1(y)$ while the other belongs to $\\Cyc^2(y)$.
\\item[(iii)] When $(a,b) \\in \\Cyc^1(y)$ and $(a',b') \\in \\Cyc^3(y)$.
\\end{itemize}
We check directly that properties (V1)-(V3) hold in cases (i), (ii), and (iii)
for each of the eight cases in Lemma~\\ref{lem-3}.
"""]

        for case, y, i, j, w in self._get_cases():
            self.y = y
            self.i = i
            self.j = j
            self.w = w
            self._tex_analysis(case)

        self.lines += ["""
\\section{Conclusion}
It follows from this exhaustive case analysis
that properties (V1)-(V3) hold for all pairs $(a,b),(a\',b\') \\in \\Cyc(y)$.
We conclude by Lemma~\\ref{lem-1} that $wt_{ij}t_{kl} \\in \\cA(y)$.
This completes the proof of the theorem.
\\end{proof}

\\begin{thebibliography}{99}

\\bibitem{BB} A. Bj\\"orner and F. Brenti,
\\emph{Combinatorics of Coxeter groups},
Graduate Texts in Mathematics 231, Springer, New York, 2005.

\\bibitem{M} E. Marberg,
On some actions of the $0$-Hecke monoids of affine symmetric groups,
\\emph{J. Combin. Theory Ser. A} \\textbf{161} (2019), 178--219.

\\end{thebibliography}

\\end{document}
"""]

    @classmethod
    def _get_cases(cls):
        cases = []
        for y in VirtualInvolution.all(maximum_size=4, mimimal_type=True):
            for i, j in itertools.combinations(range(1, y.rank + 1), 2):
                if y.tau(i, j) == y:
                    for w in y.get_virtual_atoms(required_ascents={(i, j)}):
                        cases += [(y, i, j, w)]

        dictionary = {}
        for y, i, j, w in cases:
            case = None
            if i < j == y(j) < y(i) and w(y(i)) < w(i) < w(j):
                case = 'A1'
            elif i < j < y(j) < y(i) and w(y(j)) < w(y(i)) < w(i) < w(j):
                case = 'A2'
            elif i < y(j) < j < y(i) and w(y(i)) < w(i) < w(j) < w(y(j)):
                case = 'A3'
            elif y(j) < i == y(i) < j and w(i) < w(j) < w(y(j)):
                case = 'B1'
            elif y(j) < i < y(i) < j and w(y(i)) < w(i) < w(j) < w(y(j)):
                case = 'B2'
            elif y(j) < y(i) < i < j and w(i) < w(j) < w(y(j)) < w(y(i)):
                case = 'B3'
            elif i < j < y(j) < y(i) and w(y(i)) < w(i) < w(y(j)) < w(j):
                case = 'C1'
            elif y(j) < y(i) < i < j and w(i) < w(y(i)) < w(j) < w(y(j)):
                case = 'C2'
            assert case is not None
            dictionary[case] = (y, i, j, w)
        assert set(dictionary.keys()) == {'A1', 'A2', 'A3', 'B1', 'B2', 'B3', 'C1', 'C2'}

        for case in sorted(dictionary):
            y, i, j, w = dictionary[case]
            yield case, y, i, j, w

    def _tex_analysis(self, case):
        y, i, j, w = self.y, self.i, self.j, self.w

        k, l = y.toggle(w, i, j)
        v = w.transpose(i, j).transpose(k, l)

        assert k < l
        assert y.is_virtual_atom(v)

        y_cyc, _ = self.tex_cycles(y)

        all_mirror, all_double, all_single = VirtualPermutation.maximal_extensions(w.permutation)
        virtual = VirtualPermutation(w.permutation, all_mirror, all_double, all_single)
        required_ascents = {(self.i, self.j)}
        invalid = y.get_invalid_configurations(virtual, required_ascents)

        assert w.mirror_extensions == {e: all_mirror[e] - set(invalid[e].keys()) for e in all_mirror}
        assert w.double_extensions == {e: all_double[e] - set(invalid[e].keys()) for e in all_double}
        assert w.single_extensions == {e: all_single[e] - set(invalid[e].keys()) for e in all_single}

        self.lines += ['\\section{Case %s}' % case]
        self.lines += ['Suppose $%s$ and $w^{-1} = %s$ so that $k=%s < %s=l$.' % (self.tex_order(), self.tex_list(w.permutation), self.tex_char(k), self.tex_char(l))]

        self.lines += ['\\subsection{Subcase (i)}']
        self.lines += ['In this case $v = wt_{ij}t_{kl}$ is such that']
        self.lines += ['\\begin{enumerate}\\item[]$v^{-1} = %s$.\\end{enumerate}' % self.tex_list(v.permutation)]
        self.lines += ['When $(a,b),(a\',b\')\\in\\Cyc^1(y)= %s$,' % y_cyc]
        self.lines += ['properties (V1)-(V3) are equivalent to the following conditions which evidently hold:']

        order = {b: i for i, b in enumerate(w.base)}
        cyc = {(i, y(i)) for i in range(1, y.rank + 1) if i <= y(i)}
        tuples = [(a, b, c, d) for a, b in cyc for c, d in cyc]
        self._tex_properties(order, tuples)
        self.lines += ['Thus properties (V1)-(V3) hold whenever']
        self.lines += ['$(a,b)$, $(a\',b\')$ are as in case (i) and $%s$.' % self.tex_order()]

        c = self.tex_char(VirtualPermutation.FIXED_CHAR)
        subset = '\\{i,j' + (',y_i' if y(i) != i else '') + (',y_j' if y(j) != j else '') + '\\}'
        self.lines += ['\\subsection{Subcase (ii)}']
        self.lines += ['Suppose $%s$ is an integer such that $(%s,%s) \\in \\Cyc^2(y)$, so that ' % (c, c, c)]
        self.lines += ['$%s = y_%s \\notin %s + n\\mathbb{Z}$.' % (c, c, subset)]
        self._tex_list_extensions_single(invalid, all_single)

        p, q = VirtualPermutation.CYCLE_CHARS
        p, q = self.tex_char(p), self.tex_char(q)
        self.lines += ['Next suppose $%s < %s$ are integers with $(%s, %s) \\in \\Cyc^2(y)$, so that ' % (p, q, p, q)]
        self.lines += ['$%s = y_{%s}$ and $%s,%s\\notin %s + n\\ZZ$.' % (q, p, p, q, subset)]
        self._tex_list_extensions_double(invalid, all_double)
        self.lines += ['We conclude that properties (V1)-(V3) hold whenever']
        self.lines += ['$(a,b)$, $(a\',b\')$ are as in cases (i) or (ii) and $%s$.' % self.tex_order()]

        _i, _j = self.tex_char(-i), self.tex_char(-j)
        self.lines += ['\\subsection{Subcase (iii)}']
        self.lines += ['Suppose $%s$ and $%s$ are integers such that' % (_i, _j)]
        self.lines += ['$0\\neq i - %s = j - %s \\in n\\ZZ$,' % (_i, _j)]
        self.lines += ['so that $w(i) - w(%s) = w(j) - w(%s) = i - %s$.' % (_i, _j, _i)]
        self._tex_list_extensions_mirror(invalid, all_mirror)
        self.lines += ['We conclude that properties (V1)-(V3) hold for all']
        self.lines += ['$(a,b),(a\',b\') \\in \\Cyc(y)$ when $%s$.' % self.tex_order()]

    SINGLE = 0
    DOUBLE = 1
    MIRROR = 2

    def _tex_list_extensions_single(self, invalid_dict, all_dict):
        self._tex_list_extensions(invalid_dict, all_dict, self.w.single_extensions, self.SINGLE)

    def _tex_list_extensions_double(self, invalid_dict, all_dict):
        self._tex_list_extensions(invalid_dict, all_dict, self.w.double_extensions, self.DOUBLE)

    def _tex_list_extensions_mirror(self, invalid_dict, all_dict):
        self._tex_list_extensions(invalid_dict, all_dict, self.w.mirror_extensions, self.MIRROR)

    def _tex_list_extensions(self, invalid_dictionary, all_dict, valid_dict, option):
        y, i, j, w = self.y, self.i, self.j, self.w

        start = [base for base in set(invalid_dictionary) & set(all_dict) if valid_dict[base]]
        end = [base for base in set(invalid_dictionary) & set(all_dict) if not valid_dict[base]]

        self.lines += ['\\begin{enumerate}']
        for index, base in enumerate(start + end):
            order = ' < '.join(self.tex_char(a) for a in base)
            item = '$%s$.' % (index + 1)

            if valid_dict[base]:
                self.lines += ['\\item[%s] Suppose $%s$.' % (item, order)]
            else:
                self.lines += ['\\item[%s] It cannot happen that $%s$ since:' % (item, order)]

            self.lines += ['\\begin{enumerate}[(a)]']
            items = {
                pi: self._tex_process_reasons(reasons)
                for pi, reasons in invalid_dictionary[base].items()
            }
            for pi, prop in sorted(items.items(), key=lambda pair: pair[1]):
                self.lines += ['\\item If $w^{-1} = %s$ then %s.' % (self.tex_list(pi), prop)]
            self.lines += ['\\end{enumerate}']

            if valid_dict[base]:
                k, l = y.toggle(w, i, j)
                self.lines += ['Recall that $(k,l) = (%s,%s)$.' % (self.tex_char(k), self.tex_char(l))]
                self.lines += ['We conclude that if $%s$ and then one of the following holds:' % (order)]
                self.lines += ['\\begin{enumerate}']
                for pi in valid_dict[base]:
                    t = {i: j, j: i, -i: -j, -j: -i}
                    sigma = tuple(t.get(x, x) for x in pi)

                    t = {k: l, l: k, -k: -l, -l: -k}
                    sigma = tuple(t.get(x, x) for x in sigma)

                    p, q = self.tex_list(pi), self.tex_list(sigma)
                    self.lines += ['\\item[$\\bullet$] $w^{-1} = %s$ and $v^{-1} = %s$.' % (p, q)]
                self.lines += ['\\end{enumerate}']

                plural = len(valid_dict[base]) > 1
                self._tex_conclusions(base, plural, option)

        self.lines += ['\\end{enumerate}']

    def _tex_conclusions(self, base, plural, option):
        if option == self.SINGLE:
            self._tex_single_conclusions(base, plural)
        elif option == self.DOUBLE:
            self._tex_double_conclusions(base, plural)
        elif option == self.MIRROR:
            self._tex_mirror_conclusions(base, plural)
        else:
            raise NotImplementedError

    def _tex_single_conclusions(self, base, plural):
        y = self.y

        order = {b: i for i, b in enumerate(base)}
        cyc_a = {(VirtualPermutation.FIXED_CHAR, VirtualPermutation.FIXED_CHAR)}
        cyc_b = {(i, y(i)) for i in range(1, y.rank + 1) if order[i] <= order[y(i)]}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]
        tuples += [(c, d, a, b) for a, b in cyc_a for c, d in cyc_b]

        y_cyc, _ = self.tex_cycles(y)
        c = self.tex_char(VirtualPermutation.FIXED_CHAR)

        self.lines += ['When $(a,b)= (%s, %s)$ and $(a\',b\')\\in \\Cyc^1(y)=%s$ or vice versa,' % (c, c, y_cyc)]
        self.lines += ['properties (V1)-(V3) correspond to the following conditions which hold in']
        self.lines += ['each of the available cases for $v$:']
        self._tex_properties(order, tuples)

    def _tex_double_conclusions(self, base, plural):
        y = self.y

        order = {b: i for i, b in enumerate(base)}
        cyc_a = {VirtualPermutation.CYCLE_CHARS}
        cyc_b = {(i, y(i)) for i in range(1, y.rank + 1) if order[i] <= order[y(i)]}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]
        tuples += [(c, d, a, b) for a, b in cyc_a for c, d in cyc_b]

        y_cyc, _ = self.tex_cycles(y)
        p, q = VirtualPermutation.CYCLE_CHARS
        p, q = self.tex_char(p), self.tex_char(q)

        self.lines += ['When $(a,b)= (%s,%s)$ and $(a\',b\')\\in \\Cyc^1(y)=%s$ or vice versa,' % (p, q, y_cyc)]
        self.lines += ['properties (V1)-(V3) correspond to the following conditions which hold in']
        self.lines += ['each of the available cases for $v$:']
        self._tex_properties(order, tuples)

    def _tex_mirror_conclusions(self, base, plural):
        y = self.y

        order = {b: i for i, b in enumerate(base)}
        cyc_a = {(i, y(i)) for i in range(1, y.rank + 1) if i <= y(i)}
        cyc_b = {(-i, -y(i)) for i in range(1, y.rank + 1) if i <= y(i)}

        tuples = [(a, b, c, d) for a, b in cyc_a for c, d in cyc_b]

        y_cyc, neg_y_cyc = self.tex_cycles(y)

        self.lines += ['When $(a,b)\\in\\Cyc^1(y)=%s$ and $(a\',b\')\\in%s$,' % (y_cyc, neg_y_cyc)]
        self.lines += ['properties (V1)-(V3) correspond to the following conditions which hold in']
        self.lines += ['each of the available cases for $v$:']
        self._tex_properties(order, tuples, letter='V')


def get_arguments():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        '-f',
        dest='force',
        action='store_true',
        help='force overwrite of TeX files'
    )
    return parser.parse_args()

if __name__ == '__main__':
    start = time.time()
    force = get_arguments().force

    sys.stdout.write('\nGenerating TeX files:\n\n')
    writer = CoveringPropertyTexWriter()
    if writer.write(force):
        sys.stdout.write('* Wrote proof of covering property to `%s`.\n' % writer.path)

    writer = TogglingPropertyTexWriter()
    if writer.write(force):
        sys.stdout.write('* Wrote proof of toggling property to `%s`.\n' % writer.path)

    stop = time.time()
    sys.stdout.write('\nDuration: %s seconds\n\n' % (stop - start))
