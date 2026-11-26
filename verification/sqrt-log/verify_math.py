"""Finite numerical and rational consistency checks; not a proof of uniform bounds."""
import json, math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
rng=np.random.default_rng(20261105)
ars=5.; eta=1/30; theta=.01
checks={}
checks['rate_error_constant_exact']=F(25,3)*8 <=72
checks['bonferroni_allocation_exact']=F(1,4)+3*F(1,12)==F(1,2)
checks['fixed_amplitude_exact']=F(1,30)*15==F(1,2)
checks['variance_coefficient_exact']=F(1,30)**2==F(1,900)
checks['center_coefficient_exact']=F(1,30)/3==F(1,90)
checks['final_coefficient_exact']=F(1,30)/96==F(1,2880)
checks['center_variance']=all(sum((r%2) for r in range(k))==k//2 for k in range(4,513,4))
# One deterministic sequence and a unit-circle mesh; finite sampled evidence only.
p=np.array([1]);q=np.array([1])
for _ in range(9): p,q=np.r_[p,q],np.r_[p,-q]
z=np.exp(2j*np.pi*np.arange(1024)/1024)
acc=np.zeros(1024,dtype=complex); maxprefix=0
for j in range(512):
 acc+=p[j]*z**j
 maxprefix=max(maxprefix,float(np.max(np.abs(acc))/math.sqrt(j+1)))
checks['sampled_prefix_bound']=maxprefix<=ars
res={'max_sampled_prefix_ratio':maxprefix,'prefix_constant':ars}
maxavg=maxvar=maxcov=0.
for k in [4,8,12,32,128]:
 r=np.arange(k); freq=k+r
 x=np.arange(8192)/8192
 cos=np.cos(2*np.pi*np.outer(x,freq))
 w=1+r/k
 rho=1+eta/math.sqrt(k)*(cos@(p[:k]*w))
 checks[f'density_{k}']=bool(rho.min()>=.5-1e-12 and rho.max()<=1.5+1e-12 and abs(rho.mean()-1)<1e-12)
 for _ in range(6):
  t=k/4+rng.uniform(-theta*k,theta*k)
  s=k/4+rng.uniform(-theta*k,theta*k)
  def St(v):return cos@(p[:k]*(-1.)**freq*np.sin(2*np.pi*v*w))
  st,ss=St(t),St(s)
  vt=.5*np.sin(2*np.pi*t*w)@np.sin(2*np.pi*t*w)
  vs=.5*np.sin(2*np.pi*s*w)@np.sin(2*np.pi*s*w)
  maxvar=max(maxvar,abs(np.mean(st*st)-vt))
  dk=lambda v:np.mean(np.exp(2j*np.pi*v*w))
  cov=float(np.mean(st*ss)/math.sqrt(vt*vs))
  exact=(k/4)*(dk(t-s).real-dk(t+s).real)/math.sqrt(vt*vs)
  maxcov=max(maxcov,abs(cov-exact))
  L=1+2*t/k
  avg=1+eta/math.sqrt(k)*(cos@(p[:k]*w*np.sinc(freq*L)))
  via=1+eta/(math.pi*k**1.5*L)*st
  maxavg=max(maxavg,float(np.max(np.abs(avg-via))))
checks['exact_average_sampled']=maxavg<1e-11
checks['variance_sampled']=maxvar<1e-9
checks['covariance_sampled']=maxcov<1e-10
res.update(max_average_identity_error=maxavg,max_variance_identity_error=maxvar,max_covariance_identity_error=maxcov)
a=np.exp(rng.uniform(-2,2,10000))
res['threshold_identity_max_error']=float(np.max(np.abs((a+1/a)/2-(1+(a-1)**2/(2*a)))))
checks['threshold_identity']=res['threshold_identity_max_error']<1e-13
s=np.linspace(-.5,.5,10001)
checks['log_remainder_sampled']=bool(np.all(np.abs(np.log1p(s)-s+s*s/2)<=8/3*np.abs(s)**3+1e-15))
checks['final_constant_exact']=F(1,24)*F(1,2)*F(1,2)==F(1,96)
# Check the reverse-tilt identity and eventwise interval bounds for atomic laws.
max_tilt_error=0.
for n in [16,32,64]:
 for z0 in [1.,1.5,2.]:
  y=z0/math.sqrt(n);q0=math.atanh(y);m0=z0*math.sqrt(n)
  sums=np.array([2*j-n for j in range(n+1)],dtype=float)
  raw=np.array([math.comb(n,j)/2**n for j in range(n+1)])
  psi0=math.log(math.cosh(q0));tilt=raw*np.exp(q0*sums-n*psi0)
  event=sums>=m0
  tail=float(raw[event].sum())
  reverse=float((tilt[event]*np.exp(-q0*sums[event]+n*psi0)).sum())
  max_tilt_error=max(max_tilt_error,abs(tail-reverse),abs(tilt.sum()-1))
  first=event & (sums<m0+1/q0)
  lower=math.exp(-1-q0*m0+n*psi0)*tilt[first].sum()
  lag=np.floor(q0*(sums[event]-m0))
  upper=math.exp(-q0*m0+n*psi0)*float((np.exp(-lag)*tilt[event]).sum())
  assert lower<=tail+1e-13 and tail<=upper+1e-13
checks['atomic_reverse_tilt_identity']=max_tilt_error<1e-12
checks['eventwise_interval_bounds']=True
res['max_atomic_tilt_identity_error']=max_tilt_error
assert all(checks.values()),checks
out={'scope':'Finite sampled checks and exact rational arithmetic; these checks do not replace the proof.','checks':{k:bool(v) for k,v in checks.items()},'results':res}
print(json.dumps(out,indent=2))
