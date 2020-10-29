**This is a static copy:** The framework itself is now part of the [Coq Library of Undecidability Proofs](https://github.com/uds-psl/coq-library-undecidability).

# A certifying extraction with time bounds from Coq to call-by-value λ-calculus

Yannick Forster <forster@ps.uni-saarland.de>, Fabian Kunze <kunze@ps.uni-saarland.de>, 

This repository contains the Coq formalisation of the ITP 2019 paper [A certifying extraction with time bounds from Coq to call-by-value λ-calculus](https://www.ps.uni-saarland.de/Publications/details/ForsterKunze:2019:Certifying-extraction.html).



## How to compile the code

``` shell
git clone https://github.com/uds-psl/certifying-extraction-with-time-bounds.git
cd certifying-extraction-with-time-bounds
git submodule init
git submodule update
make -j 5
```

The files are tested to compile with `The Coq Proof Assistant, version 8.8.2 (February 2019)`.

The compiled HTML version of the files can be found [here](https://uds-psl.github.io/certifying-extraction-with-time-bounds/website/toc.html) or in the `docs/website` subdirectory of this repository.
