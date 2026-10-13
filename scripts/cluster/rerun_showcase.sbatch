#!/bin/bash
#SBATCH -p cpu-fast
#SBATCH -J fshow
#SBATCH -c 2
#SBATCH --mem=64G
#SBATCH -t 04:00:00
#SBATCH -o /home1/szeider/mccert/final/logs/%x.%j.out
# Site defaults of our Slurm cluster; adjust the paths before use elsewhere.
# Showcases of the paper rerun (2026-10-02, research/eval-2026-10-02/rerun.md): one showcase per
# job through its own driver, with the private copies lean_final and tools_final; certificates in
# $SLURM_TMPDIR, results in final/results/showcases/SHOW (the driver's result.txt, T.lean,
# lean.out, plus node.txt: host, CPU, uptime at start and end, end-to-end wall, cgroup peak).
#   SHOW  tri10 | ded7 | lat7 | r35_13 | krew6 | sp7 | td9 | td10
# The graph drivers use -j = the job's CPUs (tri10 and r35_13 ran with -c 8 before).
# Usage: sbatch -C 'bc5|genoa' [-c 8] --export=ALL,SHOW=tri10 rerun_showcase.sbatch
M=/home1/szeider/mccert; F=$M/final; SC=$F/src/68fc568/scripts
L=$M/lean_final; T=$M/tools_final/bin
export PATH=$T:/home1/szeider/.elan/bin:/home1/szeider/.local/bin:$PATH
OUT=$F/results/showcases/$SHOW; W=${SLURM_TMPDIR:-/tmp/szeider.show.$$}/$SHOW
mkdir -p "$OUT" "$W"; cd "$SC" || exit 2
N=$OUT/node.txt
{ echo "host=$(hostname)"; echo "cpu=$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2 | xargs)"
  echo "affinity=$(taskset -cp $$ | cut -d: -f2 | xargs)"; echo "cpus=${SLURM_CPUS_PER_TASK:-?}"
  echo "uptime_start=$(uptime)"; echo "start=$(date -Is)"; echo "show=$SHOW"
  echo "scratch_free=$(df -hP "$W" | tail -1 | awk '{print $4}')"; } > "$N"
J=${SLURM_CPUS_PER_TASK:-2}
G=(uv run --no-project -q graph_orbits.py --work "$W/work" --lean "$L" --tools "$T" -j "$J" --inline)
D=(--out "$OUT" --work "$W/work" --lean "$L" --tools "$T")
s=$(date +%s)
case "$SHOW" in
  tri10) "${G[@]}" --family clique:3 --n 10 --out "$OUT" ;;
  r35_13) "${G[@]}" --family ramsey:3:5 --n 13 --split \
            --witness "(circulantGraph ({1, 5} : Set (Fin 13)))" --out "$OUT" ;;
  ded7) uv run --no-project -q showcase/dedekind.py --n 7 "${D[@]}" ;;
  lat7) uv run --no-project -q showcase/latin_cycles.py --n 7 --out "$OUT" --lean "$L" --tools "$T" \
          --scratch "$W" --inline ;;
  krew6) uv run --no-project -q showcase/kreweras.py --n 6 "${D[@]}" ;;
  sp7) uv run --no-project -q showcase/sperner.py --n 7 "${D[@]}" ;;
  td9) uv run --no-project -q showcase/a303210.py --n 9 "${D[@]}" ;;
  td10) uv run --no-project -q showcase/a303210.py --n 10 "${D[@]}" ;;
  *) echo "unknown SHOW $SHOW"; exit 2 ;;
esac > "$OUT/driver.log" 2>&1
e=$?
cg=$(cut -d: -f3 /proc/self/cgroup | head -1)
{ echo "driver_exit=$e"; echo "wall_s=$(( $(date +%s) - s ))"; echo "uptime_end=$(uptime)"
  echo "mem_peak_job=$(cat /sys/fs/cgroup${cg}/memory.peak 2>/dev/null || echo unknown)"; } >> "$N"
rm -rf "$W"
