# Mirror-row conjecture for N=5 role rigidity — proof attempt

## Statement (⇒ direction)

Let \(M\) be an S+D+C magma on \(\mathrm{Fin}(5)\) with absorbers \(Z=\{z_1,z_2\}\),
classifiers \(\{\tau_1,\tau_2\}\), and unique non-classifier \(g\)
(Thm 4.8). If \(|\mathrm{Aut}(M)|\ge 2\), then the transposition
\(\sigma_{\mathrm{iii}} := (\tau_1\,\tau_2)\), extended by identity on
\(Z\cup\{g\}\), is an automorphism.

## Set-up

By Functoriality (Thm 4.5) every \(\sigma\in\mathrm{Aut}(M)\) preserves the
\(Z/C/N\) partition. By Thm 4.8, \(|Z|=2\), \(|\{\tau_1,\tau_2\}|=2\), and
\(g\) is the unique non-classifier, so \(\sigma\) restricts to the group
\[
G = \mathrm{Sym}(Z)\times\mathrm{Sym}(\{\tau_1,\tau_2\})\times\{\mathrm{id}_g\}\;\cong\;\mathbb{Z}/2\times\mathbb{Z}/2.
\]
Label the four elements:
- \(\sigma_{\mathrm{i}}\) = id;
- \(\sigma_{\mathrm{ii}}\) = swap \(Z\), fix classifiers;
- \(\sigma_{\mathrm{iii}}\) = fix \(Z\), swap classifiers (the conjectured map);
- \(\sigma_{\mathrm{iv}}\) = swap \(Z\) and swap classifiers.

\(\mathrm{Aut}(M)\) is a subgroup of \(G\). Since
\(\sigma_{\mathrm{ii}}\sigma_{\mathrm{iii}}=\sigma_{\mathrm{iv}}\), at most
two of the three non-trivial elements lie in \(\mathrm{Aut}(M)\). It
suffices to rule out cases (ii) and (iv).

## Lemma A. Case (ii) is impossible.

Suppose \(\sigma_{\mathrm{ii}}\in\mathrm{Aut}(M)\). For each classifier
\(\tau_i\), the diagonal entry \(\tau_i\!\cdot\!\tau_i\) lies in \(Z\)
(definition of classifier). Applying \(\sigma_{\mathrm{ii}}\):
\[
\sigma(\tau_i\!\cdot\!\tau_i)=\sigma(\tau_i)\!\cdot\!\sigma(\tau_i)=\tau_i\!\cdot\!\tau_i,
\]
so \(\tau_i\!\cdot\!\tau_i\) is \(\sigma_{\mathrm{ii}}\)-fixed. But
\(\sigma_{\mathrm{ii}}\) fixes only \(\{\tau_1,\tau_2,g\}\), and
\(\tau_i\!\cdot\!\tau_i\in Z\) is moved. Contradiction. \(\square\)

## Lemma B. Case (iv) is impossible.

Suppose \(\sigma:=\sigma_{\mathrm{iv}}\in\mathrm{Aut}(M)\).

**Step 1: \(g\!\cdot\!g = g\).** Since \(\sigma(g)=g\),
\(\sigma(g\!\cdot\!g)=\sigma(g)\!\cdot\!\sigma(g)=g\!\cdot\!g\), so
\(g\!\cdot\!g\) is \(\sigma\)-fixed. By Thm 4.8, \(g\) is the C-triple
middle, hence core-preserving (ICP clause 1), so \(g\!\cdot\!g\in
\mathrm{core}=\{\tau_1,\tau_2,g\}\). Among these, \(\sigma\) fixes only
\(g\). Hence \(g\!\cdot\!g=g\).

**Step 2: classifier rows agree at \(g\).** By Thm 4.8 the unique C-triple
has the form \((\tau_1,g,\tau_2)\), giving the factorisation
\[
\tau_1\!\cdot\!x = \tau_2\!\cdot\!(g\!\cdot\!x)\qquad(\forall\,x\in\mathrm{core}).
\]
Setting \(x=g\) and using Step 1:
\(\tau_1\!\cdot\!g = \tau_2\!\cdot\!(g\!\cdot\!g)=\tau_2\!\cdot\!g.\)

**Step 3: classifier rows disagree at \(g\) under \(\sigma\).** Apply
\(\sigma\) to \(\tau_1\!\cdot\!g\):
\[
\sigma(\tau_1\!\cdot\!g)=\sigma(\tau_1)\!\cdot\!\sigma(g)=\tau_2\!\cdot\!g.
\]
Since \(\tau_1\!\cdot\!g\in Z\) and \(\sigma\) swaps \(Z\), this forces
\(\tau_2\!\cdot\!g\) to be the **opposite** absorber from
\(\tau_1\!\cdot\!g\); in particular \(\tau_2\!\cdot\!g\ne\tau_1\!\cdot\!g\).

Steps 2 and 3 contradict. \(\square\)

(If the C-triple has the swapped ordering \((\tau_2,g,\tau_1)\), the same
argument runs with indices flipped.)

## Main theorem (⇒).

Assume \(|\mathrm{Aut}(M)|\ge 2\). Pick a non-trivial
\(\sigma\in\mathrm{Aut}(M)\subseteq G\). By Lemmas A and B,
\(\sigma\notin\{\sigma_{\mathrm{ii}},\sigma_{\mathrm{iv}}\}\), so
\(\sigma=\sigma_{\mathrm{iii}}\). \(\square\)

## Empirical confirmation

Of the 12 non-rigid magmas in `scripts/phase_cartography_N5.json`, all 12
have \(|\mathrm{Aut}|=2\) with the lone non-trivial automorphism equal to
\(\sigma_{\mathrm{iii}}\). Exhaustive brute-force search over S+D+C tables
with absorbers fixed and \((\tau_1,\tau_2,g)=(2,3,4)\): zero examples
admit \(\sigma_{\mathrm{iv}}\). Both lemmas are corroborated.

## Status

Proof appears complete, modulo two paper-level facts already established:
- Functoriality (Thm 4.5) — used to land \(\sigma\) in \(G\);
- Thm 4.8 — uniqueness of \(g\), C-triple form \((\tau_1,g,\tau_2)\),
  and core-preservation of \(g\).

No additional hypothesis needed. The conjecture as stated is a theorem.

## Suggested formalisation

In Lean (`Magma/RigidityPartial.lean` neighbourhood), the two lemmas
discharge as follows. Given an automorphism \(\sigma\) of the table
respecting the \(Z/C/N\) partition (already produced by the existing
functoriality lemma), case-split on \(\sigma|_Z\) and
\(\sigma|_{\{\tau_1,\tau_2\}}\). Lemma A is one line: rewrite
\(\tau_i\cdot\tau_i\) and apply the homomorphism axiom. Lemma B requires
the C-triple lemma (`N5_icp_triple_structure`) plus core-preservation of
\(g\) (already in the structure-theorem file). Both are decidable
finite-case checks; `decide` or short rewriting should close them.
