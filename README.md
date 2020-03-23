# Virtual Permutations

Python project for computations involving affine and virtual permutations, as explained in the preprint "Affine transitions for involution Stanley symmetric functions" which is available online at https://arxiv.org/abs/1812.04880. 

The main results in the linked article rely on two technical theorems about the Bruhat order on affine involutions, which we refer to as the "Covering Property" (see Theorem 4.8) and the "Toggling Property" (see Theorem 4.10). Our proofs of these
results depend on computer calculations that were carried using the code in this repository.

## Setup
* Install Python 3
* Install pytest with `pip3 install pytest`

## Tests
* Run the tests at the command line with `pytest`

## Run

* Run `python3 virtual.py` to walk through the computations in an interactive mode
* The directory `/tex/` contains (very long) computer-generated proofs of the relevant properties, typeset in LaTeX
* To regenerate these `.tex` files, run `python3 tex.py -f`
