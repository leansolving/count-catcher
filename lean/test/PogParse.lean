import CountCatcherChecker.Pog

/-! The byte-level `parsePogCert` against the reference parser `parsePogCertRef` (the
    `String.splitOn` parser it replaced): the same result on every POG file of `data/`, on the
    CPOG files of `adversarial/`, on malformed variants with the expected verdict, and on all
    prefixes, deletions and single-character replacements of a small certificate. -/

open CountCatcher

/-- Both parsers agree on `s`. -/
def agree (s : String) : Bool := samePogCert (parsePogCertRef s) (parsePogCert s)

/-- Both parsers agree, and the file parses exactly when `ok`. -/
def agreeAs (ok : Bool) (s : String) : Bool := agree s && (parsePogCert s).isSome == ok

/-- All POG files of `data/`. -/
def dataPogs : List String := [
  include_str "data/a303210_3.pog",
  include_str "data/a303210_4.pog",
  include_str "data/adv_a10_reused_id.pog",
  include_str "data/adv_a14_prod_self.pog",
  include_str "data/adv_a4_prod_overlap.pog",
  include_str "data/adv_a6_self_delete.pog",
  include_str "data/adv_a7_delete_def.pog",
  include_str "data/adv_a8_leftover_derived.pog",
  include_str "data/adv_c02_neg_internal_edge.pog",
  include_str "data/adv_c03_neg_root.pog",
  include_str "data/adv_h1_unused.pog",
  include_str "data/adv_h2_or.pog",
  include_str "data/adv_h3_nand.pog",
  include_str "data/cyc10.pog",
  include_str "data/ded5.pog",
  include_str "data/dom08.pog",
  include_str "data/dom08t.pog",
  include_str "data/hq5.pog",
  include_str "data/ind08.pog",
  include_str "data/jean.pog",
  include_str "data/k4_05_2_2.pog",
  include_str "data/k4_05_2.pog",
  include_str "data/k4_05_3_2.pog",
  include_str "data/k4_05_3.pog",
  include_str "data/k4_05_4.pog",
  include_str "data/k4_05_5.pog",
  include_str "data/k4_05_t1.pog",
  include_str "data/k4_05_t10.pog",
  include_str "data/k4_05_t12.pog",
  include_str "data/k4_05_t2.pog",
  include_str "data/k4_05_t3.pog",
  include_str "data/k4_05_t5.pog",
  include_str "data/k4_05_t9.pog",
  include_str "data/k8_badA.pog",
  include_str "data/k8.pog",
  include_str "data/krew5.pog",
  include_str "data/ladder6.pog",
  include_str "data/lat5_r000.pog",
  include_str "data/lat5_r001.pog",
  include_str "data/lat5_r002.pog",
  include_str "data/lat5_r003.pog",
  include_str "data/lat5_r004.pog",
  include_str "data/lat5_r005.pog",
  include_str "data/lat5_r006.pog",
  include_str "data/lat5_r007.pog",
  include_str "data/lat5_r008.pog",
  include_str "data/lat5_r009.pog",
  include_str "data/lat5_r010.pog",
  include_str "data/lat5.pog",
  include_str "data/nohint.pog",
  include_str "data/partc_bad.pog",
  include_str "data/q08.pog",
  include_str "data/qs08_r2.pog",
  include_str "data/r33_05_2_2.pog",
  include_str "data/r33_05_5.pog",
  include_str "data/r33_05_id.pog",
  include_str "data/sp5.pog",
  include_str "data/tri05_2_2.pog",
  include_str "data/tri05_2.pog",
  include_str "data/tri05_3_2.pog",
  include_str "data/tri05_3.pog",
  include_str "data/tri05_4.pog",
  include_str "data/tri05_5.pog",
  include_str "data/tri05_id.pog",
  include_str "data/tri05_nbr0.pog",
  include_str "data/tri05_nbr1.pog",
  include_str "data/tri05_nbr2.pog",
  include_str "data/tri05_nbr3.pog",
  include_str "data/tri05_nbr4.pog",
  include_str "data/valid_empty.pog",
  include_str "data/valid_taut.pog",
  include_str "data/valid_v0.pog"]

#guard dataPogs.length = 72 && dataPogs.all fun s => agree s && (parsePogCert s).isSome

/-- The CPOG files of `adversarial/` (another format: both parsers reject them). -/
def advCpogs : List String := [
  include_str "adversarial/a10_reused_id.cpog",
  include_str "adversarial/a14_prod_self.cpog",
  include_str "adversarial/a4_prod_overlap.cpog",
  include_str "adversarial/a5_sum_input_hint.cpog",
  include_str "adversarial/a5b_sum_derived_hint.cpog",
  include_str "adversarial/a6_self_delete.cpog",
  include_str "adversarial/a7_delete_def.cpog",
  include_str "adversarial/a8_leftover_derived.cpog",
  include_str "adversarial/a9_ext_collision.cpog",
  include_str "adversarial/h1_unused.cpog",
  include_str "adversarial/h2_or.cpog",
  include_str "adversarial/h3_nand.cpog"]

#guard advCpogs.all (agreeAs false)

/-! Variants of a small certificate: `V 3`, root `5`, node 4 = `1 ∧ ¬2`, node 5 = `4 ∨ 3`. -/

def base : String := "V 3\nr 5\np 1 -2 0\ns 4 3 0:1 0\n"

#guard agreeAs true base
#guard (parsePogCert base).map (fun c => (c.pog.V, c.pog.nodes, c.hints, c.root)) ==
  some (3, #[.prod [(0, true), (1, false)], .sum (3, true) (2, true)], #[[], [⟨0, 1⟩]], (4, true))

-- Accepted: blanks around tokens, empty and blank lines, no final newline, nodes before the
-- header, `p 0` (empty product), leading zeros, `_` between digits, a huge literal, the last
-- `V` and `r` lines win (also over an earlier line that does not parse).
#guard [ "  V   3  \n\n   \nr 5\n  p  1 -2   0   \ns 4 3 0:1 0   \n\n",
    "V 3\nr 5\np 1 -2 0\ns 4 3 0:1 0",
    "p 1 -2 0\ns 4 3 0:1 0\nV 3\nr 5\n",
    "V 3\nr 4\np 0\n",
    "V 3\nr 005\np 001 -002 0\ns 4 3 00:01 0\n",
    "V 1_0\nr 5\np 1_0 -2 0\ns 4 3 0:1_1 0\n",
    "V 3\nr 5\np 123456789012345678901234567890 -2 0\n",
    "V 9\nr 5\nV 3\np 1 -2 0\n",
    "V x\nV 3\nr 0\nr 5\np 1 -2 0\n"].all (agreeAs true)

#guard (parsePogCert "V 3\nr 5\np 123456789012345678901234567890 -2 0\n").map
  (fun c => c.pog.nodes) == some #[.prod [(123456789012345678901234567889, true), (1, false)]]
#guard (parsePogCert "V 1_0\nr 5\np 1_0 0\n").map (fun c => (c.pog.V, c.pog.nodes)) ==
  some (10, #[.prod [(9, true)]])

-- Rejected: missing `V` or `r` (or one whose last value does not parse), truncated input, the
-- empty string, trailing garbage, a comment line, CRLF line ends, tabs as separators, `+`,
-- `-0`, `--1`, bad `_`, a non-ASCII byte in a number, a missing or misplaced terminator, wrong
-- arities, bad hints, a keyword glued to its argument.
#guard [ "r 5\np 1 -2 0\n", "V 3\np 1 -2 0\n", "V 3\nr 5\nV x\n", "V 3\nr 5\nr 0\n",
    "V 3\nr 5\np 1 -", "", "\n\n", "V 3\nr 5\nx\n", "V 3\nr 5\np 1 0 x\n",
    "c comment\nV 3\nr 5\n", "V 3\r\nr 5\r\np 1 -2 0\r\n", "V 3\nr 5\np 1 -2 0\r\n",
    "V 3\nr 5\np\t1 0\n", "V 3\nr 5\np 1\t0\n", "V 3\nr 5\np +1 0\n", "V +3\nr 5\n",
    "V 3\nr 5\np -0 0\n", "V 3\nr -0\n", "V 3\nr 5\np --1 0\n", "V 3\nr 5\np 1__0 0\n",
    "V 3\nr 5\np _1 0\n", "V 3\nr 5\np 1_ 0\n", "V 3\nr 5\np 1é 0\n", "V 3é\nr 5\n",
    "V 3\nr 5\np 1 -2\n", "V 3\nr 5\np\n", "V 3\nr 5\np 0 0\n", "V 3\nr 5\np 00\n",
    "V 3\nr 5\np 1 0 0\n", "V\nr 5\n", "V 3 4\nr 5\n", "V 3\nr\n", "V 3\nr 5 6\n",
    "V 3\nr 5\ns 4\n", "V 3\nr 5\ns 4 3\n", "V 3\nr 5\ns 4 3 0:1\n", "V 3\nr 5\ns 4 0 0\n",
    "V 3\nr 5\ns 4 3 : 0\n", "V 3\nr 5\ns 4 3 1: 0\n", "V 3\nr 5\ns 4 3 :1 0\n",
    "V 3\nr 5\ns 4 3 1:2:3 0\n", "V 3\nr 5\ns 4 3 1:-2 0\n", "V 3\nr 5\ns 4 3 1 0\n",
    "V3\nr 5\n", "V 3\nr5\n", "V 3\nr 5\np1 0\n", "V 3\nr 5\nP 1 0\n",
    "V 3\nr 5\npp 1 0\n"].all (agreeAs false)

/-! Systematic: every prefix, every deletion, every insertion and replacement by a character
    from a set of separators, digits, signs and letters, on two small certificates. -/

def alphabet : List Char := "0123456789 -\n\r\t+_:Vrpsxé".toList

def variants (s : String) : List String :=
  let cs := s.toList
  let n := cs.length
  (List.range (n + 1)).map (fun k => String.ofList (cs.take k)) ++
  (List.range n).map (fun k => String.ofList (cs.eraseIdx k)) ++
  ((List.range (n + 1)).flatMap fun k => alphabet.map fun c => String.ofList (cs.insertIdx k c)) ++
  ((List.range n).flatMap fun k => alphabet.map fun c => String.ofList (cs.set k c))

#guard (variants base).all agree
#guard (variants (include_str "data/nohint.pog")).all agree
