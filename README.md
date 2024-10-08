# DDF Package

This repository contains the DDF package for Mathematica.

The DDF package facilitates the DDF construction of the Feingold-Frenkel algebra.
It calculates DDF states and their commutators and then re-expresses them as DDF states.
Additionally, the package provides several operators that act on DDF states.

The functions defined in the DDF package are derived from the papers [1, 2] and adjusted to the Feingold-Frenkel algebra F.

1. R.W. Gebert and H. Nicolai, On E(10) and the DDF construction, Commun. Math. Phys. 172 (1995), 571-622, [arXiv:hep-th/9406175](https://arxiv.org/abs/hep-th/9406175).
2. R.W. Gebert and H. Nicolai, An Affine string vertex operator construction at arbitrary level, J. Math. Phys. 38 (1997), 4435-4450, [arXiv:hep-th/9608014](https://arxiv.org/abs/hep-th/9608014).

## Getting Started

To get started clone this repository to your local machine.

```
git clone https://github.com/hmalcha/DDF.git ddf
```

Alternatively, you can download the contents of this repository by clicking on **Code** and then **Download Zip** in the top right corner.

After cloning the repository open and run the Mathematica notebook **User_Guide.nb**. It contains a brief introduction to the DDF package and explains all the functions and symbols that the package provides.

## Usage

For the DDF package consist of the package file ***ddf.wl*** and the two folders **ddf_states** and **schur_polynomials**. These folders contain many pre-computed DDF states and Schur polynomials. The package file and the folders must be placed in the same directory.

To load the package into a Mathematica notebook write:

```
Get["ddf.wl"]
```

## Compute new DDF States

Besides the two folders, the user guide and the package file there is one more file in this repository. The Wolfram Language Script file **compute_ddf_states.wls** computes DDF states and stores them in the folder **ddf_states**.

Because the file is a *.wls* file it requires *wolframscript* to be installed and must be called from the command line via

```
wolframscript -file compute_ddf_states.wls [LEVEL] [WEIGHT]
```

The placeholders [LEVEL] and [WEIGHT] must be replaced by two integers.

The *.wls* script then computes all DDF states of the given level and weight up to mode sum 7.

It is advised to comment out the parts of this script that compute the DDF states with mode sum 4 and higher before running it on your local machine. At the moment it takes about 60 hours (on a powerful server) to run the entire script for arbitrary values of LEVEL and WEIGHT.

## License
Copyright © 2024 Hannes Malcha

The DDF Package is free software: you can redistribute it and/or modify it under the terms of the GNU General Public License as published by the Free Software Foundation, either version 3 of the License, or (at your option) any later version.
The DDF Package is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
You should have received a copy of the GNU General Public License along with the DDF Package. If not, see https://www.gnu.org/licenses/.

