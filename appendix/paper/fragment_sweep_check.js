// Conservative scan-minus-retention margin at query 256, conditional on an ordinary prefix.
// Node receives an exported deterministic fixture. No sampled ranks enter this state space.
'use strict';
const fs=require('fs');
const data=JSON.parse(fs.readFileSync(process.argv[2],'utf8'));
const {classes:C,Q,H,h,K}=data;
function localWarm(size){
    let floor=data.hot_floor;
    for(let a=0;a<data.M;a+=size){
        const ids=[];
        for(let j=a;j<Math.min(data.M,a+size);j++)if(data.first_cold[j])ids.push(j);
        const all=(1<<ids.length)-1;
        const dp=new Float64Array(all+1).fill(Infinity);
        dp[0]=0;
        const cls=ids.map(j=>C.find(c=>c.members.includes(j)).mask);
        for(let seen=0;seen<all;seen++){
            const open=ids.map((_,i)=>i).filter(i=>!(seen & (1<<i)));
            function cost(i,peer){
                const j=ids[i], [n,threshold]=data.first_cold[j];
                let depth=h+1;
                for(const k of open)if(k!==i && k!==peer)depth=Math.min(depth,32-Math.clz32(j^ids[k]));
                const buddy=ids.indexOf(j^1);
                const interior=ids[peer]===(j^1) || (buddy>=0 && (seen & (1<<buddy)) &&
                                    data.first_cold[j^1][2]<=threshold);
                const lower=7*n-32-4*h+3*Math.max(0,h+1-depth);
                const benefit=interior?lower:Math.min(4*n-29-h,lower);
                return open.length>1?benefit:Math.min(0,benefit);
            }
            for(const i of open){
                const one=seen|(1<<i);
                dp[one]=Math.min(dp[one],dp[seen]+cost(i,-1));
                for(const j of open)if(j>i && cls[j]!==cls[i]){
                    const two=one|(1<<j);
                    dp[two]=Math.min(dp[two],dp[seen]+cost(i,j)+cost(j,i));
                }
            }
        }
        floor+=dp[all];
    }
    return floor;
}
data.warm_floor=Math.max(data.warm_floor,localWarm(8));
const sides=Array.from({length:8},(_,s)=>C.map((g,c)=>((g.mask>>(s>>1))&1)===(s%2)?c:-1).filter(i=>i>=0));
const R=C.reduce((a,c)=>a+c.warm,0);
const first=Math.ceil(Math.min(...sides.map(side=>side.reduce((a,c)=>a+C[c].warm,0)))/2);
const maxExtra=R-2*first;
const base=512;
const inc=Array.from({length:6},(_,c)=>c===5?0:base**c);
const decode=(key,total)=>{
    const v=[];
    for(let i=0;i<5;i++){v.push(key%base);key=Math.floor(key/base);}
    v.push(total-v.reduce((a,b)=>a+b,0));return v;
};
const layers=Array.from({length:Q},()=>new Set());
for(let z=0;z<6;z++){
    const options=sides.filter(side=>!side.includes(z));
    let active=new Set([0]);
    for(let s=0;s<=maxExtra;s++){
        const t=(R+s)/2;
        const next=new Set();
        for(const key of active){
            const v=decode(key,s);
            if(Number.isInteger(t))layers[t].add(key);
            for(const side of options){
                const high=Math.max(...side.map(g=>C[g].picks[v[g]][0]));
                for(const g of side)if(C[g].picks[v[g]][0]===high)next.add(key+inc[g]);
            }
        }
        active=next;
    }
}
const trees=C.map(g=>{
    const t=[new Int32Array(2*H).fill(-1),new Int32Array(2*H).fill(-1)];
    for(let i=0;i<g.members.length;i++)for(let k=0;k<2;k++)t[k][H+g.members[i]]=g.initial[i][k];
    for(let k=0;k<2;k++)for(let j=H-1;j;j--)t[k][j]=Math.max(t[k][2*j],t[k][2*j+1]);
    return g.picks.map(p=>{
        const result=t.map(a=>a.slice());
        for(let k=0;k<2;k++){
            let j=H+p[1];t[k][j]=p[2+k];
            for(j>>=1;j;j>>=1)t[k][j]=Math.max(t[k][2*j],t[k][2*j+1]);
        }
        return result;
    });
});
const maxNode=(arr,node)=>Math.max(arr[0][node],arr[1][node],arr[2][node],arr[3][node],arr[4][node],arr[5][node]);
function gain(arr,p,k){
    const join=32-Math.clz32(p[0][1]^p[1][1]);
    const cold=[[],[]];
    for(let side=0;side<2;side++){
        let j=H+p[side][1];
        for(let d=1;d<=h;d++){cold[side].push(maxNode(arr,j^1));j>>=1;}
    }
    const below=cold.map(a=>Math.max(-1,...a.slice(0,join-1)));
    cold[0][join-1]=below[1];cold[1][join-1]=below[0];
    const fresh=p.some(task=>task[5]); // a background on its last possible visits; see handling below
    let sum=0,bonus=0;
    for(let side=0;side<2;side++){
        const [n,first,last]=p[side][4][k];
        if(!n)continue;
        const y0=maxNode(arr,H+p[1-side][1]),y1=p[1-side][2+k];
        const cursor=x=>{let d=0;while(d<h && cold[side][d]<=x)d++;return d;};
        const cl=cursor(first),ch=cursor(last);
        const low=Math.min(h,cl+1,Math.max(y0,y1)>first?join:h);
        const high=Math.min(h,ch+1,Math.min(y0,y1)>last?join:h);
        bonus+=12*n*(low-(k===0?data.hotJoin:1));
        if(n<4 || low===high)continue;
        const end=k===0?ch:cl, begin=k===0?cl:ch,bound=k===0?h:0;
        const kk=end!==bound?n:Number(begin!==bound);
        const movement=fresh?Math.abs(end-(k===0?0:h)):Math.abs(end-begin);
        sum+=7*n+3*(movement+kk)-32-3*n-4*h;
    }
    return [sum,bonus];
}
// Mark only a *second* background visit. Its first visit is in the saturation sweep;
// if it occurs at the boundary the single 12h correction covers all four groups.
for(let c=0;c<6;c++){
    const initial=new Set(C[c].members.filter((j,i)=>C[c].initial[i][0]===0));
    for(const p of C[c].picks){
        p[5]=initial.delete(p[1]);
    }
}
const kmax=Math.max(...data.covers.map(c=>c[0].length+c[1].length));
const bills=C.map(g=>{
    const n=g.revision_sum.slice();
    return g.picks.map(p=>{
        const value=17*n[1]+(4+12*data.hotJoin)*n[0];
        for(let k=0;k<2;k++)n[k]+=p[4][k][0];
        return value;
    });
});
function prefixF(t,v){
    let obsolete=0;
    for(let q=0;q<t;q++)obsolete+=Math.min(data.lis,2*q);
    return (36*32+23+4*h-5*(3*kmax+1))*t -10*obsolete
        + v.reduce((a,b,c)=>a+bills[c][b],0) - 5*data.fee - 4*data.M;
}
function scanInfo(arr,side){
    let best=-1,ties=0,obsolete=0;
    for(const j of side){
        const x=maxNode(arr,j);
        if(x>best){obsolete+=ties;best=x;ties=1;}
        else if(x===best)ties++;
    }
    return [obsolete,ties];
}
let current=new Map(),visited=0;
const baselines={};
for(let t=Math.ceil(R/2);t<Q;t++){
    for(const key of layers[t]){
        const f=prefixF(t,decode(key,2*t-R));
        const old=current.get(key)??[Infinity,Infinity];
        current.set(key,[Math.min(data.warm_floor-12*h,old[0]),Math.min(f,old[1])]);
    }
    visited+=current.size;
    if((t+1)%64===0 || t===Q-1){
        let min=Infinity,minf=Infinity;
        for(const v of current.values()){min=Math.min(v[0],min);minf=Math.min(v[1],minf);}
        baselines[t+1]=[current.size,min,minf];
    }
    if(t===Q-1)break;
    const next=new Map();
    for(const [key,g] of current){
        const v=decode(key,2*t-R);
        const p=C.map((c,i)=>c.picks[v[i]]);
        const lower=v.map((x,i)=>trees[i][x][0]);
        const upper=v.map((x,i)=>trees[i][x][1]);
        const anchor=maxNode(lower,1);
        const permitted=new Set();
        for(let i=0;i<6;i++)if(lower[i][1]===anchor)
            for(let a=0;a<4;a++)if(C[i].mask & (1<<a))permitted.add(a);
        const choices=new Set();
        for(const a of permitted){
            const inside=sides[2*a+1],outside=sides[2*a];
            const x=Math.max(...inside.map(i=>p[i][0])), y=Math.max(...outside.map(i=>p[i][0]));
            if(y-anchor<=K/80)continue;
            for(const i of inside)if(p[i][0]===x)for(const j of outside)if(p[j][0]===y)
                choices.add(Math.min(i,j)*6+Math.max(i,j));
        }
        for(const code of choices){
            const i=Math.floor(code/6),j=code%6,pair=[p[i],p[j]];
            const dest=key+inc[i]+inc[j];
            const gl=gain(lower,pair,0),gu=gain(upper,pair,1);
            const value=g[0]+gl[0]+gu[0];
            let query=-Infinity;
            for(const a of permitted){
                const sides=data.covers[a];
                const ob=scanInfo(upper,sides[0])[0]+scanInfo(upper,sides[1])[0];
                query=Math.max(query,5*(3*(sides[0].length+sides[1].length)+1)+10*ob);
            }
            const fee=36*32+23+4*h-query+bills[i][v[i]+1]-bills[i][v[i]]
                    +bills[j][v[j]+1]-bills[j][v[j]];
            const f=g[1]+fee+gl[1]+gu[1];
            const old=next.get(dest)??[Infinity,Infinity];
            next.set(dest,[Math.min(value,old[0]),Math.min(f,old[1])]);
        }
    }
    current=next;
}
const total=2*(Q-1)-R;
if(process.argv[3])fs.writeFileSync(process.argv[3],JSON.stringify(Array.from(current,([key,v])=>[decode(key,total),...v])));
const kmin=Math.min(...data.covers.map(c=>c[0].length+c[1].length));
let earlyCredit=data.fee;
for(let t=0;t<128;t++){
    const hi=Math.min(kmax,Math.max(0,R-t-Math.min(t,first)));
    const lo=Math.max(0,kmin-2*t);
    if(lo>hi)throw new Error('inconsistent cover-count bounds');
    let maxWrites=0;
    for(let k=lo;k<=hi;k++)maxWrites=Math.max(maxWrites,Math.min(2*kmax-k,k+2*data.lis));
    earlyCredit+=3*kmax+1+maxWrites;
}
process.stdout.write(JSON.stringify({R,maxExtra,visited,warm_floor:data.warm_floor,baselines,earlyCredit,
        gate:8*(68*data.M+96),clipLower:baselines[Q][2]+23+4*h-5*(3*kmax+1)-10*data.lis})+'\n');

