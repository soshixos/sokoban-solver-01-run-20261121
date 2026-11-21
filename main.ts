import*as fs from"node:fs";
const{MAKEFUN_INPUT_DIR:I="/input",MAKEFUN_OUTPUT_DIR:O="/output"}=process.env;
let w,A,G,B,P,D,N,seen,mark,par,stm=0;
const S="udlr",T="UDLR";
function parse(t){w=t.indexOf("\n");t=t.replace(/\n/g,"");N=t.length;A=new Uint8Array(N);G=[];B=[];for(let i=0;i<N;i++){let c=t[i];A[i]=c=="#";if(A[i])continue;if(".*+".includes(c))G.push(i);if("$*".includes(c))B.push(i);if("@+".includes(c))P=i}D=[-w,w,-1,1];seen=[];mark=[];par=[]}
function reach(o,f,a,r){let t=++stm,q=[f],l=f;a[f]=t;while(q.length){let p=q.pop();if(p<l)l=p;for(let k=0;k<4;k++){let y=p+D[k];if(!A[y]&&!o[y]&&a[y]!=t){a[y]=t;if(r)par[y]=k;q.push(y)}}}return l}
function solve(g,b,p,o){let oc=new Uint8Array(N),q=[[b,p,""]],ix=new Set;for(let x of o)oc[x]=1;for(let[bs,pl,s]of q){for(let x of bs)oc[x]=1;reach(oc,pl,seen,1);let he=stm;for(let x of bs)for(let k=0;k<4;k++){let d=D[k],t=x+d;if(seen[x-d]!=he||A[t]||oc[t])continue;let u=x-d,v="";for(let y=u;y!=pl;y-=D[par[y]])v=S[par[y]]+v;let nb=bs.slice();nb[bs.indexOf(x)]=t;nb.sort((a,b)=>a-b);oc[x]=0;oc[t]=1;let nk=reach(oc,x,mark)+","+nb;oc[t]=0;oc[x]=1;if(ix.has(nk))continue;ix.add(nk);let ns=s+v+T[k];if(nb+""==g+"")return[ns,x];q.push([nb,x,ns])}for(let x of bs)oc[x]=0}return null}
function solveLevel(t){parse(t);let R=x=>((x/w|0)>(P/w|0))+2*((x%w/7)|0),rb=[[],[],[],[]],rg=[[],[],[],[]],p=P,m="";for(let x of B)rb[R(x)].push(x);for(let x of G)rg[R(x)].push(x);for(let r in rb){if(!rb[r].length)continue;let o=[].concat(...rb.filter((_,j)=>j!=r));let z=solve(rg[r],rb[r],p,o);if(z==null)return"";m+=z[0];p=z[1];rb[r]=rg[r]}return m}
for(let i=1;i<6;i++){let d="i00"+i,z=solveLevel(fs.readFileSync(I+"/"+d+"/level.txt","utf8"));fs.mkdirSync(O+"/"+d,{recursive:true});fs.writeFileSync(O+"/"+d+"/solution.txt",z+"\n")}
