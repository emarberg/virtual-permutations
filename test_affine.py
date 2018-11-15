from affine import AffinePermutation


def test_constructor():
    # constructor requires list of at least two integers
    try:
        AffinePermutation()
        assert False
    except:
        pass

    try:
        AffinePermutation(3)
        assert False
    except:
        pass

    try:
        AffinePermutation([3])
        assert False
    except:
        pass

    # valid constructions
    w = AffinePermutation(1, 2)
    assert all(w(i) == i for i in range(10))
    w = AffinePermutation(2, 1)
    assert all(w(i) == (i + 1) if i % 2 else (i - 1) for i in range(10))

    # constructor takes single list, single tuple, or variable length integer args
    w = AffinePermutation(3, 2, 5, 12)
    x = AffinePermutation([3, 2, 5, 12])
    y = AffinePermutation((3, 2, 5, 12))
    assert w == x == y

    # input args must represent each congruence class exactly once
    try:
        AffinePermutation(3, 2, 5, 15)
        assert False
    except:
        pass


def test_star():
    n = 6
    for i in range(n):
        s = AffinePermutation.simple_transposition(i, n)
        t = AffinePermutation.simple_transposition(n - i, n)
        assert s.star() == t
        assert t.star() == s

    i = [1, 2, 6, 4, 3, 4, 2, 5, 6]
    w = AffinePermutation.identity(n)
    v = AffinePermutation.identity(n)
    for a in i:
        w *= AffinePermutation.simple_transposition(a, n)
        v *= AffinePermutation.simple_transposition(a, n).star()

    assert w.star() == v


def test_identity():
    # rank is required to be at least 2
    try:
        AffinePermutation.identity(0)
        assert False
    except:
        pass

    try:
        AffinePermutation.identity(1)
        assert False
    except:
        pass

    w = AffinePermutation.identity(2)
    assert w == AffinePermutation(1, 2) == AffinePermutation(-1, 0)
    assert w.rank == 2
    assert w.is_identity()
    assert w.is_involution()

    w = AffinePermutation.identity(3)
    assert w == AffinePermutation(1, 2, 3) == AffinePermutation(2, 3, 4)
    assert w.rank == 3
    assert w.is_identity()
    assert w.is_involution()


def test_s_i():
    assert AffinePermutation.simple_transposition(-1, 2) == AffinePermutation(2, 1)
    assert AffinePermutation.simple_transposition(0, 2) == AffinePermutation(0, 3)
    assert AffinePermutation.simple_transposition(1, 2) == AffinePermutation(2, 1)
    assert AffinePermutation.simple_transposition(2, 2) == AffinePermutation(0, 3)

    assert AffinePermutation.simple_transposition(1, 3) == AffinePermutation(2, 1, 3)
    assert AffinePermutation.simple_transposition(2, 3) == AffinePermutation(1, 3, 2)
    assert AffinePermutation.simple_transposition(3, 3) == AffinePermutation(0, 2, 4)
    assert AffinePermutation.simple_transposition(4, 3) == AffinePermutation(2, 1, 3)
    assert AffinePermutation.simple_transposition(5, 3) == AffinePermutation(1, 3, 2)
    assert AffinePermutation.simple_transposition(6, 3) == AffinePermutation(0, 2, 4)

    w = AffinePermutation.simple_transposition(5, 50)
    assert w(5) == 6
    assert w(6) == 5
    assert w(55) == 56
    assert w(56) == 55
    assert all(w(i) == i for i in range(100) if i not in [5, 6, 55, 56])


def test_transposition():
    for n in range(10):
        for i in range(n):
            for j in range(n * n):
                if i % n == j % n or j < i:
                    try:
                        AffinePermutation.transposition(i, j, n)
                        assert False
                    except:
                        pass
                else:
                    t = AffinePermutation.transposition(i, j, n)
                    assert t(i) == j
                    assert t(i + n) == j + n
                    assert t(j) == i
                    assert t(j + n) == i + n
                    assert all(t(k) == k for k in range(n) if (k % n) not in [i % n, j % n])
                    assert j > i + 1 or t == AffinePermutation.simple_transposition(i, n)


def test_inverse():
    r = AffinePermutation.simple_transposition(1, 3)
    s = AffinePermutation.simple_transposition(2, 3)
    t = AffinePermutation.simple_transposition(3, 3)

    assert r.inverse() == r
    assert (r * s).inverse() == s * r
    assert (r * s * t).inverse() == t * s * r
    assert (r * s * t * r).inverse() == r * t * s * r
    assert (r * s * t * r * s).inverse() == s * r * t * s * r
    assert (r * s * t * r * s * t).inverse() == t * s * r * t * s * r

    w = r * s * t * r * s * t
    assert w.inverse() == w**-1


def test_multiplication():
    w = AffinePermutation(3, 5, -6, 11, 2)
    v = AffinePermutation(5, 6, 3, 54, 7)

    # the magic function * implements ordinary group multiplication
    x = w * v
    assert all(x(i) == w(v(i)) for i in range(50))

    x = v * w
    assert all(x(i) == v(w(i)) for i in range(50))

    # the magic function % implements the Demazure product
    assert w % v == AffinePermutation([46, -5, -8, -2, -16])
    assert v % w == AffinePermutation([-5, -4, -17, 49, -8])

    s = AffinePermutation.simple_transposition(1, 5)
    t = AffinePermutation.simple_transposition(2, 5)
    u = AffinePermutation.simple_transposition(3, 5)

    assert s * s == AffinePermutation.identity(5)
    assert s % s == s
    assert s * t * u == s % t % u
    assert s * t * s * t == t * s
    assert s % t % s % t == s * t * s == t * s * t


def test_lt():
    assert AffinePermutation(1, 2, 3) < AffinePermutation(1, 3, 2)
    assert not (AffinePermutation(1, 2, 3) < AffinePermutation(1, 2, 3))
    assert not (AffinePermutation(1, 3, 2) < AffinePermutation(1, 2, 3))


def test_length():
    w = AffinePermutation.identity(3)
    assert len(w) == w.length == 0
    assert w.absolute_length == 0
    assert w.involution_length == 0

    r = AffinePermutation.simple_transposition(1, 3)
    s = AffinePermutation.simple_transposition(2, 3)
    t = AffinePermutation.simple_transposition(3, 3)

    assert len(r) == 1
    assert len(r * s) == 2
    assert len(r * s * t) == 3
    assert len(r * s * t * r) == 4
    assert len(r * s * t * r * s) == 5
    assert len(r * s * t * r * s * t) == 6

    assert r.involution_length == 1
    assert (s * r * s).involution_length == 2
    assert (t * s * r * s * t).involution_length == 3
    assert (r * t * s * r * s * t * r).involution_length == 4
    assert (s * r * t * s * r * s * t * r * s).involution_length == 5
    assert (t * s * r * t * s * r * s * t * r * s * t).involution_length == 6

    t = AffinePermutation.transposition(2, 7, 6)
    assert t.absolute_length == 1

    u = AffinePermutation.transposition(3, 91, 6)
    assert u.absolute_length == 1

    assert (u * t).absolute_length == 2

    w = AffinePermutation(3, 5, -6, 11, 2)
    assert w.length == 15


def test_cycle_set():
    w = AffinePermutation(3, 5, -6, 11, 2)
    assert w.cycle_set == {(0, -3), (1, 3, -6)}
    assert w.absolute_length == 3


def test_descents():
    w = AffinePermutation(3, 5, -6, 11, 2)
    assert w.right_descent_set == {2, 4}
    assert w.left_descent_set == {2, 4, 5}
    assert w.right_ascent_set == {1, 3, 5}
    assert w.left_ascent_set == {1, 3}

    w = AffinePermutation.identity(5)
    assert w.right_descent_set == set()
    assert w.left_descent_set == set()
    assert w.right_ascent_set == {1, 2, 3, 4, 5}
    assert w.left_ascent_set == {1, 2, 3, 4, 5}


def test_codes():
    for i in range(4):
        for j in range(4):
            for k in range(4):
                a = [0] + [i, j, k]
                b = [i] + [0] + [j, k]
                c = [i, j] + [0] + [k]
                d = [i, j, k] + [0]
                assert AffinePermutation.from_code(a).code == tuple(a)
                assert AffinePermutation.from_code(b).code == tuple(b)
                assert AffinePermutation.from_code(c).code == tuple(c)
                assert AffinePermutation.from_code(d).code == tuple(d)

    assert AffinePermutation([1, 2, 3, 4, 5]).code == (0, 0, 0, 0, 0)
    assert AffinePermutation([0, 2, 3, 4, 6]).code == (0, 0, 0, 0, 1)
    assert AffinePermutation([-1, 2, 3, 5, 6]).code == (0, 0, 0, 1, 1)
    assert AffinePermutation([-2, 2, 4, 5, 6]).code == (0, 0, 1, 1, 1)
    assert AffinePermutation([0, 1, 2, 4, 8]).code == (0, 0, 0, 0, 3)
    assert AffinePermutation([-1, 1, 3, 5, 7]).code == (0, 0, 0, 1, 2)
    assert AffinePermutation([-3, 3, 4, 5, 6]).code == (0, 1, 1, 1, 1)


def test_reduced_words():
    w = AffinePermutation.identity(5)
    assert w.reduced_words == {tuple()}

    r = AffinePermutation.simple_transposition(1, 3)
    s = AffinePermutation.simple_transposition(2, 3)
    t = AffinePermutation.simple_transposition(3, 3)

    assert r.reduced_words == {(1,)}
    assert (r * s).reduced_words == {(1, 2)}
    assert (r * s * t).reduced_words == {(1, 2, 3)}
    assert (r * s * t * r).reduced_words == {(1, 2, 3, 1)}
    assert (r * s * t * r * s).reduced_words == {(1, 2, 3, 1, 2)}
    assert (r * s * t * r * s * t).reduced_words == {(1, 2, 3, 1, 2, 3)}

    assert (r * s * r).reduced_words == {(1, 2, 1), (2, 1, 2)}

    n = 5
    w = AffinePermutation(*reversed(range(1, n + 1)))
    words = w.reduced_words
    assert len(words) == 768
    for e in words:
        v = AffinePermutation.identity(n)
        for i in e:
            v *= AffinePermutation.simple_transposition(i, n)
        assert v == w


def test_involution_words():
    w = AffinePermutation.identity(5)
    assert w.involution_words == {tuple()}

    r = AffinePermutation.simple_transposition(1, 3)
    s = AffinePermutation.simple_transposition(2, 3)
    t = AffinePermutation.simple_transposition(3, 3)

    # can only access this property for affine permutations which are involutions
    assert (r * s).involution_words is None

    assert r.involution_words == {(1,)}
    assert (s * r * s).involution_words == {(1, 2), (2, 1)}
    assert (t * s * r * s * t).involution_words == {(1, 2, 3), (2, 1, 3)}
    assert (r * t * s * r * s * t * r).involution_words == {
        (1, 2, 3, 1), (2, 1, 3, 1), (2, 3, 1, 3), (3, 2, 1, 3)
    }

    n = 5
    w = AffinePermutation(*reversed(range(1, n + 1)))
    words = w.involution_words
    assert len(words) == 80
    for e in words:
        v = AffinePermutation.identity(n)
        for i in e:
            s = AffinePermutation.simple_transposition(i, n)
            v = s % v % s
        assert v == w


def test_atoms():
    z = AffinePermutation.transposition(1, 8, 4) * AffinePermutation.transposition(2, 7, 4)
    u = AffinePermutation(4, 6, 1, -1)
    v = AffinePermutation(6, 4, -1, 1)
    assert z.is_involution()
    assert u.is_atom()
    assert v.is_atom()
    assert z.get_min_atom() == u
    assert z.get_max_atom() == v
    assert len(list(z.get_atoms())) == 3
    assert set(z.get_atoms()) == {u, v, AffinePermutation(5, 6, -1, 0)}

    t1 = AffinePermutation.transposition(1, 12, 6)
    t2 = AffinePermutation.transposition(2, 11, 6)
    t3 = AffinePermutation.transposition(3, 4, 6)
    z = t1 * t2 * t3
    assert z.is_involution()
    assert z.get_min_atom() == AffinePermutation(4, 6, 8, 7, -1, -3)
    assert z.get_max_atom() == AffinePermutation(10, 8, 0, -1, 1, 3)
    assert len(list(z.get_atoms())) == 29
