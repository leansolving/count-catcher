#!/bin/bash
# Build D4, cpog-gen/cpog-check, CaDiCaL, drat-trim on the Slurm cluster (Debian 13).
# Same commits as the Mac build. Run on slurm-login01 (needs git, curl, boost headers).
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
set -euo pipefail
T=/home1/szeider/mccert/tools
mkdir -p "$T" && cd "$T"

clone() { [ -d "$2" ] || git clone -q "https://github.com/$1.git" "$2"; (cd "$2" && git checkout -q "$3"); }
clone crillab/d4 d4 333370c
clone rebryant/cpog cpog a97ed85
clone arminbiere/cadical cadical c6073042
clone marijnheule/drat-trim drat-trim 2e3b2dc

# --enable-fat: runtime CPU dispatch. Without it GMP is tuned to the build host (the Ice Lake
# login node) and D4 dies with SIGILL on the Zen2 compute nodes once counts get large.
if [ ! -f gmp/lib/libgmpxx.a ]; then
  curl -sSLO https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz
  tar xf gmp-6.3.0.tar.xz
  (cd gmp-6.3.0 && ./configure --enable-cxx --enable-fat --disable-shared --with-pic --prefix="$T/gmp" > ../gmp.log 2>&1 \
     && make -j8 >> ../gmp.log 2>&1 && make install >> ../gmp.log 2>&1)
fi

# Same one-line patch as on the Mac (undefined base-class virtual method).
sed -i 's|^  virtual T computeNbModels();|  virtual T computeNbModels() { assert(0); return T(); }|' d4/DAG/DAG.hh
(cd d4 && make -j8 CXX="g++ -std=c++14 -I$T/gmp/include" LDFLAGS="-L$T/gmp/lib -no-pie" > ../d4.log 2>&1)
# cpog-check a97ed85 prints two debug lines per clause lookup unconditionally (98 MB log and
# 50x slowdown on domino 8x8); guard them behind verbosity 4.
sed -i -e 's|^    printf("Looking for clause %d.  Got block|    if (verb_level >= 4) printf("Looking for clause %d.  Got block|' \
       -e 's|^\tprintf("Looking for clause %d.  lid = |\tif (verb_level >= 4) printf("Looking for clause %d.  lid = |' cpog/src/cpog-check.c
(cd cpog/src && make install > ../../cpog.log 2>&1)
(cd cadical && ./configure > ../cadical.log 2>&1 && make -j8 >> ../cadical.log 2>&1)
# GCC 14 rejects the implicit getc_unlocked under -std=c99, so build with gnu99.
(cd drat-trim && gcc drat-trim.c -std=gnu99 -O2 -o drat-trim > ../drat.log 2>&1)

mkdir -p bin
ln -sf ../d4/d4 bin/d4
ln -sf ../cadical/build/cadical bin/cadical
ln -sf ../drat-trim/drat-trim bin/drat-trim
ln -sf ../cpog/src/cpog-gen bin/cpog-gen
ln -sf ../cpog/src/cpog-check bin/cpog-check
ls -la bin/
