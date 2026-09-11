"""Check that the IsSidon / maxSidonSubsetCard / h definitions in our E30.lean are
character-identical (modulo whitespace) to google-deepmind/formal-conjectures."""
import re, json, hashlib, os

ROOT = r'C:\Users\jared\Local Sites\woocommerce-enterprise'
FC_BASIC = os.path.join(ROOT, 'oracle', 'acquisition', 'formal-conjectures',
                        'FormalConjecturesForMathlib', 'Combinatorics', 'Basic.lean')
FC_30 = os.path.join(ROOT, 'oracle', 'acquisition', 'formal-conjectures',
                     'FormalConjectures', 'ErdosProblems', '30.lean')
OURS = os.path.join(ROOT, 'oracle', 'evidence', 'msl-machine', 'campaigns',
                    'erdos30-close-2026-09-05', 'lean', 'E30.lean')


def norm(t):
    return re.sub(r'\s+', ' ', t).strip()


def grab(text, start, end=None):
    i = text.index(start)
    j = text.index(end, i) if end else len(text)
    return text[i:j]


fc_basic = open(FC_BASIC, encoding='utf-8').read()
fc30 = open(FC_30, encoding='utf-8').read()
ours_full = open(OURS, encoding='utf-8').read()
# skip the header docstring, which QUOTES the FC file verbatim
ours = ours_full[ours_full.index('namespace E30'):]

results = {}

# 1. IsSidon
fc_issidon = grab(fc_basic, 'def IsSidon (A : Set α) : Prop', 'namespace Set')
our_issidon = grab(ours, 'def IsSidon (A : Set α) : Prop', 'instance (A : Finset α)')
results['IsSidon_identical'] = norm(fc_issidon) == norm(our_issidon)
results['IsSidon_fc'] = norm(fc_issidon)
results['IsSidon_ours'] = norm(our_issidon)

# 2. maxSidonSubsetCard
fc_max = grab(fc_basic, 'def maxSidonSubsetCard (A : Finset α)', '/-- If `A` is finite Sidon')
our_max = grab(ours, 'def maxSidonSubsetCard (A : Finset α)', "/-- `h N`")
results['maxSidonSubsetCard_identical'] = norm(fc_max) == norm(our_max)
results['maxSidonSubsetCard_fc'] = norm(fc_max)
results['maxSidonSubsetCard_ours'] = norm(our_max)

# 3. h
fc_h = grab(fc30, 'noncomputable abbrev h (N : \u2115)', '\n\n')
our_h = grab(ours, 'noncomputable abbrev h (N : \u2115)', '\n\n')
results['h_fc'] = norm(fc_h)
results['h_ours'] = norm(our_h)
# FC's is Finset.maxSidonSubsetCard (namespaced); ours is the local copy
results['h_same_modulo_namespace'] = (
    norm(fc_h).replace('Finset.maxSidonSubsetCard', 'maxSidonSubsetCard')
    == norm(our_h))

# 4. the Decidable instance
fc_dec = grab(fc_basic, 'instance (A : Finset α) [DecidableEq α] : Decidable', '/-- The maximum size')
our_dec = grab(ours, 'instance (A : Finset α) [DecidableEq α] : Decidable', '/-- The maximum size')
results['Decidable_instance_identical'] = norm(fc_dec) == norm(our_dec)

results['sha256_E30_lean'] = hashlib.sha256(open(OURS, 'rb').read()).hexdigest()
results['sha256_FC_Basic_lean'] = hashlib.sha256(open(FC_BASIC, 'rb').read()).hexdigest()
results['sha256_FC_30_lean'] = hashlib.sha256(open(FC_30, 'rb').read()).hexdigest()

print(json.dumps(results, indent=1, ensure_ascii=False))
