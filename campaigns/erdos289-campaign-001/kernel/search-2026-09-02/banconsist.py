"""Consistency gate: P1-ban search vs no-ban search must give identical verdicts."""
import sys, time
sys.path.insert(0,'.')
from search289 import Board, search_shard, shard_range
fails=0
for B in (60,100,140,180):
    b0=Board(B,p1ban=False); b1=Board(B,p1ban=True)
    for k in range(1,9):
        r=[]
        for bd in (b0,b1):
            t=time.time(); ex=True; wit=None; tot=0
            for a1 in shard_range(bd,k):
                o,p,n=search_shard(bd,k,a1,10**9); tot+=n
                if o=='WITNESS': wit=p; break
            r.append((wit is not None, wit, tot, time.time()-t))
        same = (r[0][0]==r[1][0])
        if not same: fails+=1; print("MISMATCH",B,k,r[0][:2],r[1][:2])
        print("B=%3d k=%d noban(exists=%s nodes=%9d %.2fs)  ban(exists=%s nodes=%9d %.2fs) speedup=%.1fx"%(
            B,k,r[0][0],r[0][2],r[0][3],r[1][0],r[1][2],r[1][3],(r[0][2]+1)/(r[1][2]+1)))
print("BAN-CONSISTENCY:", "PASS" if fails==0 else "FAIL")
