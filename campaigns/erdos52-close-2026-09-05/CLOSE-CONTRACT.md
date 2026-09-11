MSL_DIALECT v2.0
MSL_PROFILE MSL-F
MSL_MODE CLOSE

SOURCE E52
  CITATION Erdos Problem 52, erdosproblems.com/52, the sum-product problem, prize 250 USD
  FINGERPRINT 747343f8181c23fba16c1a4ff6667b3bf3e169714813fde05859525f6d017273
  ACCESSED oracle/evidence/formalizer-sources/erdos/raw-erdos-52.html frozen snapshot 2026-08-30
  SOURCE_COVERAGE PARTIAL
  OBJECT_INVENTORY GENERATOR the frozen html page plus FormalConjectures/ErdosProblems/52.lean
  UNHARVESTED the 23 page comments and the linked complete sum-product history webpage

TARGET_IDENTITY T52
  SOURCE E52
  SOURCE_STATEMENT Let A be a finite set of integers. Is it true that for every epsilon greater than zero max of the size of A plus A and the size of A times A is much greater than the size of A raised to two minus epsilon
  SOURCE_FINGERPRINT 747343f8181c23fba16c1a4ff6667b3bf3e169714813fde05859525f6d017273
  FORMAL_STATEMENT for all real epsilon with zero less than epsilon less than one there exists real C greater than zero such that for every finite set A of integers the real cast of max of the card of A plus A and the card of A times A is at least C times the real cast of the card of A to the power two minus epsilon
  BINDING TRANSCRIPTION_CERT
  BINDING_WITNESS Erdos52Frag.SumProduct in lean/Erdos52Frag.lean
  OPERATION additive sumset and multiplicative product set of one finite integer set
  ARITH_FN NONE
  TARGET_LOCK LOCKED

CLOSE_CONTRACT CC52
  TARGET T52
  PROOF_REQUIRES a proof that for every epsilon in the open unit interval a positive constant C exists making the displayed inequality hold for every finite set of integers
  DISPROOF_REQUIRES a proof exhibiting an epsilon in the open unit interval for which no positive constant C works, that is an infinite family of finite integer sets whose max sumset product set size is smaller than any fixed constant times the cardinality to the two minus epsilon
  NOT_CLOSURE STANDARD_FLOOR
  NOT_CLOSURE an improved exponent below two minus epsilon, including any advance on the current record 1962 over 1469
  NOT_CLOSURE the refutation over the reals of Bloom Sawin Schildkraut Zhelezov, which does not speak about integers
  NOT_CLOSURE a bound over a finite field, the complex numbers, or higher fold sum and product sets
  FROZEN_WITH T52
