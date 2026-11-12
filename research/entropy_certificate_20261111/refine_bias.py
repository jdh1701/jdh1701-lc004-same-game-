"""Exact rational common-bias refinement, retaining original potentials/policy."""
from fractions import Fraction
from decimal import Decimal, localcontext
from pathlib import Path
import json
p=Path(__file__).parent
m=(p/'prefix9-1.txt').read_text().splitlines()
c=(p/'tilted10-9.certificate.txt').read_text().splitlines()
n,q,hi,lo=map(int,c[0].split()); rows=[list(map(int,s.split())) for s in c[1:]]
lower=Fraction(0);upper=None;lower_witness=None;upper_witness=None
for s in m[1:]:
 t=s.split();i,k=map(int,t[:2]);v=list(map(int,t[2+k:]))
 for b in range(2):
  d=[v[2*(3*b+a)+1]*q+rows[v[2*(3*b+a)]][1]-rows[i][1] for a in range(3)]
  total=sum(d);fav=d[rows[i][2+b]]
  if fav<0 and Fraction(total,-fav)>lower:
   lower=Fraction(total,-fav);lower_witness=[i,b,total,fav]
  elif fav>0 and (upper is None or Fraction(-total,fav)<upper):
   upper=Fraction(-total,fav);upper_witness=[i,b,total,fav]
  elif fav==0: assert total<0
low=100000000
extra=lower.numerator*low//lower.denominator+1
ratio=Fraction(extra,low)
assert ratio>lower and (upper is None or ratio<upper) and ratio<Fraction(1,9)
high=low+extra;den=high+2*low
out=p/'refined-bias.certificate.txt'
out.write_text(f'{n} {q} {high} {low}\n'+'\n'.join(c[1:])+'\n')
with localcontext() as ctx:
 ctx.prec=60
 entropy=Decimal(den).ln()-(Decimal(high)*Decimal(high).ln()+2*Decimal(low)*Decimal(low).ln())/Decimal(den)
 rate=entropy.exp()
print(json.dumps({'lower_open_threshold':str(lower),'upper_open_threshold':str(upper),
 'lower_witness_state_back_sum_favored':lower_witness,'upper_witness_state_back_sum_favored':upper_witness,
 'selected_excess_bias':str(ratio),'weights':[high,low,low],
 'growth_decimal_display_only':str(rate),
 'scope':'Optimal common-bias interval for this fixed potential and fixed favorites only; not global optimization.'},indent=2))
