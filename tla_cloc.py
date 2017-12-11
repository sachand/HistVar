import sys

with open(sys.argv[1]) as f:
	content = f.readlines()
content = [x.strip() for x in content]

count_line = 0
count_cmt = 0
in_comment = 0
cont_lemmas = -20
set_inc = 0
spec_size = 0
prf_contra = 0
for line in content:
	count_line += 1
	if line == '' or line[:2] in ['\\*', '==', '--']:
		count_cmt += 1
		continue
	
	if in_comment :
		count_cmt += 1

	if line[:2] == '(*' :
		count_cmt += 1

	if '(*' in line : in_comment = 1
	
	if not in_comment:
		if 'Spec == Init /\ [][Next]_vars' in line:
			spec_size = count_line - count_cmt
			count_line = 0
			count_cmt = 0
		
		if 'Phase1aVotedForInv' in line : cont_lemmas += 1
		if 'Phase1aWontVoteIn' in line : cont_lemmas += 1
		if 'Phase1aAccepted' in line : cont_lemmas += 1

		if 'Phase1bVotedForInv' in line : cont_lemmas += 1
		if 'Phase1bWontVoteIn' in line : cont_lemmas += 1
		if 'Phase1bAccepted' in line : cont_lemmas += 1

		if 'Phase2bVotedForInv' in line : cont_lemmas += 1
		if 'Phase2bWontVoteIn' in line : cont_lemmas += 1
		if 'Phase2bAccepted' in line : cont_lemmas += 1

		if 'Phase2a1VotedForInv' in line : cont_lemmas += 1
		if 'Phase2a1WontVoteIn' in line : cont_lemmas += 1
		if 'Phase2a1Accepted' in line : cont_lemmas += 1

		if 'Phase2a11VotedForInv' in line : cont_lemmas += 1
		if 'Phase2a11WontVoteIn' in line : cont_lemmas += 1
		if 'Phase2a11Accepted' in line : cont_lemmas += 1

		if 'Phase2a12VotedForInv' in line : cont_lemmas += 1
		if 'Phase2a12WontVoteIn' in line : cont_lemmas += 1
		if 'Phase2a12Accepted' in line : cont_lemmas += 1

		if 'Phase2a13VotedForInv' in line : cont_lemmas += 1
		if 'Phase2a13WontVoteIn' in line : cont_lemmas += 1
		if 'Phase2a13Accepted' in line : cont_lemmas += 1

		if 'Phase2aVotedForInv' in line : cont_lemmas += 1
		if 'Phase2aWontVoteIn' in line : cont_lemmas += 1
		if 'Phase2aAccepted' in line : cont_lemmas += 1

		if 'SafeAtStable' in line : cont_lemmas += 1
		
		if 'CASE m \\in msgs' in line : set_inc += 1
		if 'CASE mm \\in msgs' in line : set_inc += 1
		if 'CASE ma \\in msgs' in line : set_inc += 1
		if 'CASE m2 \\in msgs' in line : set_inc += 1

		if 'CASE m \\in sent' in line : set_inc += 1
		if 'CASE mm \\in sent' in line : set_inc += 1
		if 'CASE ma \\in sent' in line : set_inc += 1
		if 'CASE m2 \\in sent' in line : set_inc += 1
		
		if 'PROVE' in line and 'FALSE' in line : prf_contra += 1
	
	if '*)' in line : in_comment = 0

print('Spec size excluding comments {}'.format(spec_size))	
print('Proof size excluding comments {}'.format(count_line - count_cmt))
print('Proofs by contradiction {}'.format(prf_contra))
#print('Cont lemmas {}'.format(cont_lemmas))
#print('Set Incs {}'.format(set_inc))
