// Enclose all post-saturation class counts in integer boxes. Merge only within
// the same grid cell, and forget correlations only in the outward direction.
'use strict';
const {Q,K,classes:C}=JSON.parse(require('fs').readFileSync(process.argv[2],'utf8'));
const width=32, radix=512, inc=C.map((_,i)=>radix**i);
const sides=Array.from({length:8},(_,s)=>C.map((c,i)=>((c.mask>>(s>>1))&1)===(s%2)?i:-1).filter(i=>i>=0));
const R=C.reduce((a,c)=>a+c.warm,0);
const first=Math.ceil(Math.min(...sides.map(side=>side.reduce((a,i)=>a+C[i].warm,0)))/2);
const t0=R-first;
const sum=a=>a.reduce((x,y)=>x+y,0);
function tighten(lo,hi,total){
    let a=sum(lo),b=sum(hi);
    if(a>total || b<total)return false;
    for(let i=0;i<6;i++){
        const l=Math.max(lo[i],total-b+hi[i]),h=Math.min(hi[i],total-a+lo[i]);
        if(l>h)return false;
        lo[i]=l;hi[i]=h;
    }
    return true;
}
function insert(map,lo,hi,total){
    if(!tighten(lo,hi,total))return;
    let key=0;
    for(let i=0;i<6;i++){
        const k=Math.floor(lo[i]/width);
        if(Math.floor(hi[i]/width)!==k){
            const mid=(k+1)*width;
            const x=hi.slice(),y=lo.slice();
            x[i]=mid-1;y[i]=mid;
            insert(map,lo.slice(),x,total);insert(map,y,hi.slice(),total);return;
        }
        key+=k*inc[i];
    }
    if(!Number.isSafeInteger(key))throw new Error('cell packing exceeds exact integer range');
    const old=map.get(key);
    if(!old){map.set(key,[lo,hi]);return;}
    for(let j=0;j<6;j++){old[0][j]=Math.min(old[0][j],lo[j]);old[1][j]=Math.max(old[1][j],hi[j]);}
}
let boxes=new Map(),total=2*t0-R;
insert(boxes,C.map(()=>0),C.map(c=>Math.min(total,t0-c.warm)),total);
let visited=0,peak=0,history={},t=t0;
for(;t<Q-1 && boxes.size;t++,total+=2){
    peak=Math.max(peak,boxes.size);visited+=boxes.size;
    if(((t+1)&t)===0)history[t+1]=boxes.size;
    const next=new Map();
    for(const [lo,hi] of boxes.values()){
        const l=lo.map((v,i)=>C[i].rows[v]);
        const u=hi.map((v,i)=>C[i].rows[v]);
        const anchor=Math.max(...l.map(r=>r[1]));
        let owners=0;for(let i=0;i<6;i++)if(u[i][2]>=anchor)owners|=C[i].mask;
        for(let a=0;a<4;a++)if(owners & (1<<a)){
            const out=sides[2*a],ins=sides[2*a+1];
            const umin=Math.max(...ins.map(i=>u[i][0])),vmin=Math.max(...out.map(i=>u[i][0]),anchor+K/80+1);
            for(const i of ins)if(l[i][0]>=umin)for(const j of out)if(l[j][0]>=vmin){
                const x=lo.slice(),y=hi.slice();
                for(const [picked,group,lower] of [[i,ins,umin],[j,out,vmin]]){
                    while(y[picked]>=x[picked] && C[picked].rows[y[picked]][0]<lower)y[picked]--;
                    for(const k of group)if(k!==picked){
                        while(x[k]<=y[k] && C[k].rows[x[k]][0]>l[picked][0])x[k]++;
                    }
                }
                if(x.some((v,k)=>v>y[k]))continue;
                x[i]++;y[i]++;x[j]++;y[j]++;
                insert(next,x,y,total+2);
            }
        }
    }
    boxes=next;
}
console.log(JSON.stringify({warm:t0,boxes_visited:visited,peak_boxes:peak,last:t+1,remaining:boxes.size,history}));

