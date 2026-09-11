/* C(12,5,2): exhaustive decision "is there a covering of size <= MAXB?"
 * Complete branching: at each node take the least uncovered pair and branch
 * over every 5-subset containing it.  Root WLOG: one block is {0,1,2,3,4}
 * (relabelling).  Prunes: (P1) uncovered <= 10*rem;
 * (P2) for each point x, ceil(u_x/4) <= rem, and sum_x ceil(u_x/4) <= 5*rem.
 * Prints the search node count and the verdict; a found cover is printed for
 * independent re-verification by a separate program.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 U128;
static inline int pc(U128 v){return __builtin_popcountll((unsigned long long)v)+__builtin_popcountll((unsigned long long)(v>>64));}

#define N 12
#define NP 66
static int pidx[N][N];
static U128 FULLM;
static int nb = 0;
static int blk[792][5];
static U128 bm[792];
static int thru[NP][120], nthru[NP];
static U128 atmask[N];
static int MAXB = 8;
static long long nodes = 0;
static int found = 0, sol[16][5], soln = 0;

static void gen(void){
  int i,j,a,b,c,d,e,k=0;
  for(i=0;i<N;i++) for(j=i+1;j<N;j++) pidx[i][j]=pidx[j][i]=k++;
  FULLM = (((U128)1<<k)-1);
  for(a=0;a<N;a++)for(b=a+1;b<N;b++)for(c=b+1;c<N;c++)for(d=c+1;d<N;d++)for(e=d+1;e<N;e++){
    int v[5]={a,b,c,d,e}; U128 m=0; int p,q;
    for(p=0;p<5;p++)for(q=p+1;q<5;q++) m|=(U128)1<<pidx[v[p]][v[q]];
    memcpy(blk[nb],v,sizeof v); bm[nb]=m; nb++;
  }
  for(i=0;i<NP;i++) nthru[i]=0;
  for(i=0;i<nb;i++){ int p,q; for(p=0;p<5;p++)for(q=p+1;q<5;q++){ int id=pidx[blk[i][p]][blk[i][q]]; thru[id][nthru[id]++]=i; } }
  for(i=0;i<N;i++){ atmask[i]=0; for(j=0;j<N;j++) if(j!=i) atmask[i]|=(U128)1<<pidx[i][j]; }
}

static int prune(U128 cov,int rem){
  U128 u = FULLM & ~cov;
  int unc = pc(u);
  if(unc > 10*rem) return 1;
  int tot=0,x;
  for(x=0;x<N;x++){ int ux=pc(u & atmask[x]); int need=(ux+3)/4;
    if(need>rem) return 1; tot+=need; }
  if(tot > 5*rem) return 1;
  return 0;
}

static void dfs(U128 cov,int depth,int cur[][5]){
  if(found) return;
  nodes++;
  if(cov==FULLM){ found=1; soln=depth; memcpy(sol,cur,sizeof(int)*5*depth); return; }
  int rem=MAXB-depth;
  if(rem==0 || prune(cov,rem)) return;
  int least=-1,i;
  for(i=0;i<NP;i++) if(!((cov>>i)&(U128)1)){ least=i; break; }
  for(i=0;i<nthru[least];i++){
    int bi=thru[least][i];
    memcpy(cur[depth],blk[bi],sizeof(int)*5);
    dfs(cov|bm[bi],depth+1,cur);
    if(found) return;
  }
}

int main(int argc,char**argv){
  if(argc>1) MAXB=atoi(argv[1]);
  gen();
  static int cur[16][5];
  int b0[5]={0,1,2,3,4}; U128 m0=0; int p,q;
  for(p=0;p<5;p++)for(q=p+1;q<5;q++) m0|=(U128)1<<pidx[b0[p]][b0[q]];
  memcpy(cur[0],b0,sizeof b0);
  dfs(m0,1,cur);
  printf("{\"n\":12,\"k\":5,\"t\":2,\"max_blocks\":%d,\"candidate_blocks\":%d,\"pairs\":%d,",MAXB,nb,NP);
  printf("\"root_block_fixed_wlog\":[0,1,2,3,4],\"search_nodes\":%lld,",nodes);
  if(!found){ printf("\"verdict\":\"EXHAUSTED_NO_COVER\",\"conclusion\":\"C(12,5,2) > %d\"}\n",MAXB); }
  else { int i,j; printf("\"verdict\":\"COVER_FOUND\",\"cover\":[");
    for(i=0;i<soln;i++){ printf("%s[",i?",":""); for(j=0;j<5;j++) printf("%s%d",j?",":"",sol[i][j]); printf("]"); }
    printf("],\"conclusion\":\"C(12,5,2) <= %d\"}\n",soln); }
  return 0;
}
