from virtual import VirtualInvolution, VirtualPermutation
from affine import AffinePermutation
import itertools


def test_virtualize_fixed():
    y = AffinePermutation(5, 4, 3, 2, 1, 6, 7)
    w = AffinePermutation(5, 1, 3, 4, 2, 6, 7).inverse()
    i = 3
    j = 6

    assert w in y.get_atoms()
    v = w.virtualize(i, j, y)
    assert v.base == (1, 2)
    assert v.permutation == (1, 2)

    assert {key: val for key, val in v.mirror_extensions.items() if val} == {
        (-1, -2, 1, 2): {(-1, -2, 1, 2)},
    }

    a = VirtualPermutation.FIXED_CHAR
    assert {key: val for key, val in v.single_extensions.items() if val} == {
        (1, 2, a): {(1, 2, a)},
        (a, 1, 2): {(a, 1, 2)},
    }

    a, b = VirtualPermutation.CYCLE_CHARS
    assert {key: val for key, val in v.double_extensions.items() if val} == {
        (1, 2, a, b): {(1, 2, b, a)},
        (a, b, 1, 2): {(b, a, 1, 2)},
        (a, 1, b, 2): {(b, a, 1, 2), (1, b, a, 2)},
    }


def test_virtualize_cycle():
    y = AffinePermutation(6, 5, 4, 3, 2, 1, 7)
    w = AffinePermutation(5, 2, 4, 3, 6, 1, 7).inverse()
    i = 3
    j = 14

    assert w in y.get_atoms()
    v = w.virtualize(i, j, y)
    assert v.base == (1, 2, 3)
    assert v.permutation == (2, 1, 3)

    assert {key: val for key, val in v.mirror_extensions.items() if val} == {
        (-1, -2, -3, 1, 2, 3): {(-2, -1, -3, 2, 1, 3)},
        (-1, -2, 1, 2, -3, 3): {(-2, -1, 2, 1, -3, 3)},
    }

    assert {key: val for key, val in v.single_extensions.items() if val} == {}

    a, b = VirtualPermutation.CYCLE_CHARS
    assert {key: val for key, val in v.double_extensions.items() if val} == {
        (1, 2, 3, a, b): {(2, 1, 3, b, a)},
        (a, b, 1, 2, 3): {(b, a, 2, 1, 3)},
        (1, 2, a, b, 3): {(2, 1, b, a, 3)},
        (a, 1, 2, b, 3): {(b, a, 2, 1, 3), (2, 1, b, a, 3)},
    }


def test_is_atom():
    y = AffinePermutation(6, 5, 4, 3, 2, 1, 7)
    i = 3
    j = 14

    y_, i_, j_ = VirtualInvolution.from_permutation(y, i, j)
    for w in y.get_atoms():
        w_ = w.virtualize(i, j, y)
        assert y_.is_virtual_atom(w_)
        assert i_ == 1 and j_ == 3


def test_transpose():
    y = AffinePermutation(6, 5, 4, 3, 2, 1, 7)
    i, j = 3, 7

    y_, i_, j_ = VirtualInvolution.from_permutation(y, i, j)

    assert i_ == 1 and j_ == 3

    w = AffinePermutation(6, 1, 4, 3, 5, 2, 7).inverse()
    w_ = w.virtualize(3, 7, y)

    assert y_.is_virtual_atom(w_)

    z_ = y_.tau(i_, j_)
    v_ = w_.transpose(i_, j_)

    a, b = VirtualPermutation.CYCLE_CHARS
    assert not z_.is_virtual_atom(v_)
    assert z_.get_invalid_configurations(v_) == {
        (a, 1, 2, b, 3): {(2, 3, b, a, 1): [(y_.REASON_C2, ('P', 'Q', 1, 3))]}
    }


def test_get_virtual_atoms():
    y = AffinePermutation(6, 5, 4, 3, 2, 1, 7)
    i, j = 1, 6

    y_, i_, j_ = VirtualInvolution.from_permutation(y, i, j)
    assert list(y_.get_virtual_atoms(required_ascents={(i_, j_)})) == []

    atoms = list(y_.get_virtual_atoms())
    assert len(atoms) == 1

    virtual = atoms[0]
    for w in y.get_atoms():
        assert virtual.contains(w.virtualize(i, j, y))


def test_all():
    assert set(VirtualInvolution.all(3, False)) == {
        VirtualInvolution((1, 1), (2, 2)),
        VirtualInvolution((1, 2)),
        #
        VirtualInvolution((1, 1), (2, 2), (3, 3)),
        VirtualInvolution((1, 2), (3, 3)),
        VirtualInvolution((1, 1), (2, 3)),
        VirtualInvolution((1, 1), (2, 3)),
        VirtualInvolution((1, 3), (2, 2)),
    }


def test_toggling_property():
    a = list(VirtualInvolution.all(maximum_size=4, mimimal_type=True))
    for index, y in enumerate(a):
        print('Left:', len(a) - index)
        for i, j in itertools.combinations(range(1, y.rank + 1), 2):
            z = y.tau(i, j)
            if y == z:
                for w in y.get_virtual_atoms(required_ascents={(i, j)}):
                    print('y =', y)
                    print('w =', w)
                    assert y.rank in {3, 4}
                    if y.rank == 3:
                        assert y.cycles == {(1, 3)} and y.fixed == {2}
                    if y.rank == 4:
                        assert y.cycles == {(1, 4), (2, 3)} and y.fixed == set()

                    k, l = y.toggle(w, i, j)
                    v = w.transpose(i, j).transpose(k, l)
                    print('v == w?\n', v == w)
                    print('v =', v)
                    assert y.is_virtual_atom(v)


def test_covering_property():
    a = list(VirtualInvolution.all(maximum_size=4, mimimal_type=True))
    for index, y in enumerate(a):
        print('Left:', len(a) - index)
        for i, j in itertools.combinations(range(1, y.rank + 1), 2):
            z = y.tau(i, j)
            if y != z:
                for w in y.get_virtual_atoms(required_ascents={(i, j)}):
                    print('y =', y)
                    print('z =', z)
                    print('w =', w)
                    print('w * t_{i,j} =', w.transpose(i, j))
                    assert z.is_virtual_atom(w.transpose(i, j))
