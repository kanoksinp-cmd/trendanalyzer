// Trend Analyzer — บอทเซิร์ฟเวอร์ (รันบน GitHub Actions ทุก 5 นาที ไม่ต้องเปิดเว็บ)
// ใช้กฎชุดเดียวกับหน้าเว็บ: ยืนยันเมื่อปิดแท่ง + กรองเทรนด์ TF ใหญ่ + เวลาตลาดทอง + งดเทรดช่วงข่าวแรง USD
// ตั้งค่าผ่าน GitHub → Settings → Secrets and variables → Actions (ดู README-bot.md)
'use strict';
const fs=require('fs'),path=require('path');
const E=(k,d)=>{const v=process.env[k];return v===undefined||v===''?d:v;};
const CONF={
  token:E('TG_TOKEN'),chat:E('TG_CHAT'),
  asset:E('ASSET','GOLD'),tf:E('TF','15m'),horizon:+E('HORIZON',3),speed:E('SPEED','normal'),mode:E('MODE','strict'),
  htf:E('HTF_MODE','block'),news:E('NEWS_BLOCK','on'),cost:E('COST_PCT',''),offset:+E('OFFSET',0),
  bal:+E('ACC_BAL',0),cur:E('ACC_CUR','THB'),fx:+E('FX',33),riskPct:+E('RISK_PCT',1),oz:+E('OZ_PER_LOT',100),
  sendWait:E('SEND_WAIT','off')==='on',
};
const SPEEDS={normal:{f:9,s:21,t:50,r:14,m:[12,26,9]},fast:{f:5,s:13,t:34,r:9,m:[8,17,9]},turbo:{f:3,s:8,t:21,r:7,m:[5,13,5]}};
const CFG=SPEEDS[CONF.speed]||SPEEDS.normal,N9='EMA'+CFG.f,N21='EMA'+CFG.s,N50='EMA'+CFG.t;
const TF_SEC={'1m':60,'5m':300,'15m':900,'1h':3600,'4h':14400,'1d':86400};
const HTF_MAP={'1m':'15m','5m':'1h','15m':'1h','1h':'4h','4h':'1d'};
const NAMES={GOLD:'Gold (XAU/USD)',BTCUSDT:'Bitcoin',ETHUSDT:'Ethereum',SOLUSDT:'Solana',BNBUSDT:'BNB',XRPUSDT:'XRP',DOGEUSDT:'Dogecoin'};
const STATE_FILE=path.join(__dirname,'state.json');
const isGold=CONF.asset==='GOLD',SYM=isGold?'PAXGUSDT':CONF.asset;

// ---------------- core (คัดลอกจากหน้าเว็บ ให้ผลตรงกัน) ----------------
function ema(arr,p){const k=2/(p+1);const out=new Array(arr.length).fill(null);let prev=null;
  for(let i=0;i<arr.length;i++){if(i<p-1)continue;
    if(prev===null){let s=0;for(let j=i-p+1;j<=i;j++)s+=arr[j];prev=s/p;}else prev=arr[i]*k+prev*(1-k);
    out[i]=prev;}return out;}
function rsi(c,p=14){const out=new Array(c.length).fill(null);let g=0,l=0;
  for(let i=1;i<c.length;i++){const d=c[i]-c[i-1];const up=Math.max(d,0),dn=Math.max(-d,0);
    if(i<=p){g+=up;l+=dn;if(i===p){g/=p;l/=p;out[i]=l===0?100:100-100/(1+g/l);}}
    else{g=(g*(p-1)+up)/p;l=(l*(p-1)+dn)/p;out[i]=l===0?100:100-100/(1+g/l);}}
  return out;}
function macd(c,m=[12,26,9]){const e12=ema(c,m[0]),e26=ema(c,m[1]);const line=c.map((_,i)=>e12[i]!=null&&e26[i]!=null?e12[i]-e26[i]:null);
  const start=line.findIndex(v=>v!=null);const sig=new Array(c.length).fill(null);
  if(start>=0){const s=ema(line.slice(start),m[2]);s.forEach((v,i)=>sig[start+i]=v);}
  return line.map((v,i)=>v!=null&&sig[i]!=null?v-sig[i]:null);}
function atr(h,l,c,p=14){const tr=c.map((_,i)=>i===0?h[0]-l[0]:Math.max(h[i]-l[i],Math.abs(h[i]-c[i-1]),Math.abs(l[i]-c[i-1])));
  const out=new Array(c.length).fill(null);let a=null;
  for(let i=0;i<c.length;i++){if(i<p-1)continue;if(a===null){let s=0;for(let j=i-p+1;j<=i;j++)s+=tr[j];a=s/p;}else a=(a*(p-1)+tr[i])/p;out[i]=a;}
  return out;}
function levelsAt(h,l,c,i,lookback=150,w=3,minD=0){const start=Math.max(w,i+1-lookback),price=c[i];let sup=null,res=null;
  for(let k=start;k<=i-w;k++){let isH=true,isL=true;
    for(let j=k-w;j<=k+w;j++){if(h[j]>h[k])isH=false;if(l[j]<l[k])isL=false;}
    if(isH&&h[k]>price+minD&&(res===null||h[k]<res))res=h[k];
    if(isL&&l[k]<price-minD&&(sup===null||l[k]>sup))sup=l[k];}
  return {sup,res};}
function tradeLevels(side,P,A,S,R){
  if(side==='LONG'){let sl=(S!=null&&P-S<2*A)?S-0.3*A:P-1.5*A;if(P-sl<0.6*A)sl=P-0.8*A;const risk=P-sl;
    const tp1=(R!=null&&R-P>=risk)?R:P+1.5*risk;let tp2=P+2.5*risk;if(tp2<=tp1+0.3*risk)tp2=tp1+risk;
    return {entryLow:Math.max(S!=null?S:-Infinity,P-0.5*A),entryHigh:P,sl,tp1,tp2,risk,rr:(tp1-P)/risk,tooClose:R!=null&&R-P<0.8*risk};}
  let sl=(R!=null&&R-P<2*A)?R+0.3*A:P+1.5*A;if(sl-P<0.6*A)sl=P+0.8*A;const risk=sl-P;
  const tp1=(S!=null&&P-S>=risk)?S:P-1.5*risk;let tp2=P-2.5*risk;if(tp2>=tp1-0.3*risk)tp2=tp1-risk;
  return {entryLow:P,entryHigh:Math.min(R!=null?R:Infinity,P+0.5*A),sl,tp1,tp2,risk,rr:(P-tp1)/risk,tooClose:S!=null&&P-S<0.8*risk};}
function scoreAt(i,I){const {c,e9,e21,e50,r,mh}=I;
  if(i<3||[e9[i],e21[i],e50[i],r[i],mh[i],e21[i-2]].some(v=>v==null))return null;
  const v=[];
  v.push([`ราคาเทียบ ${N9} (ไวสุด)`,c[i]>e9[i]?1:-1,c[i]>e9[i]?'ราคายืนเหนือเส้นเร็ว':'ราคาอยู่ใต้เส้นเร็ว']);
  v.push([`${N9} เทียบ ${N21}`,e9[i]>e21[i]?1:-1,e9[i]>e21[i]?`${N9} อยู่เหนือ (โมเมนตัมขึ้น)`:`${N9} อยู่ใต้ (โมเมนตัมลง)`]);
  v.push([`ราคาเทียบ ${N50}`,c[i]>e50[i]?1:-1,c[i]>e50[i]?'ราคาเหนือเส้นเทรนด์':'ราคาใต้เส้นเทรนด์']);
  v.push(['MACD Histogram',mh[i]>0?1:-1,mh[i]>0?'เป็นบวก':'เป็นลบ']);
  const rv=r[i];let rs=0,rt='กลางๆ';
  if(rv>=70){rs=0;rt='ซื้อมากเกิน ระวังย่อ';}else if(rv>55){rs=1;rt='ฝั่งซื้อได้เปรียบ';}
  else if(rv<=30){rs=0;rt='ขายมากเกิน ระวังเด้ง';}else if(rv<45){rs=-1;rt='ฝั่งขายได้เปรียบ';}
  v.push([`RSI(${CFG.r}) = `+rv.toFixed(1),rs,rt]);
  const sl=e21[i]-e21[i-2];
  v.push([`ความชัน ${N21}`,sl>0?1:-1,sl>0?'ชันขึ้น':'ชันลง']);
  return {score:v.reduce((a,x)=>a+x[1],0),votes:v};}
function probFrom(buckets,score){const b=buckets[score];
  if(b&&b.n>=15)return {p:b.up/b.n,n:b.n,same:true};
  let nn=0,uu=0;for(const k in buckets){if(Math.sign(+k)===Math.sign(score)){nn+=buckets[k].n;uu+=buckets[k].up;}}
  return nn?{p:uu/nn,n:nn,same:false}:null;}
function decide(score,p,n,mode){
  if(score>0&&p>=0.52)return 'LONG';if(score<0&&p<=0.48)return 'SHORT';
  if(mode==='stat'&&n>=30&&Math.abs(p-0.5)>=0.05)return p>0.5?'LONG':'SHORT';
  return null;}
function manageTrade(pos,hi,lo,cl,i,maxHold=50){const L=pos.side==='LONG',r=pos.risk,P=pos.P,mv=x=>(L?x-P:P-x)/r;
  const hitSL=L?lo<=pos.sl:hi>=pos.sl;
  if(hitSL)return {R:pos.half?0.5*pos.r1+0.5*mv(pos.sl):mv(pos.sl),why:pos.half?'TP1+ทุน':'SL'};
  if(!pos.half&&(L?hi>=pos.tp1:lo<=pos.tp1)){pos.half=true;pos.r1=mv(pos.tp1);pos.sl=P;}
  if(pos.half&&(L?hi>=pos.tp2:lo<=pos.tp2))return {R:0.5*pos.r1+0.5*mv(pos.tp2),why:'TP2'};
  if(i-pos.i0>=maxHold)return {R:pos.half?0.5*pos.r1+0.5*mv(cl):mv(cl),why:'หมดเวลา'};
  return null;}
const NYF=new Intl.DateTimeFormat('en-US',{timeZone:'America/New_York',weekday:'short',hour:'numeric',hourCycle:'h23'});
function goldOpen(ms){const p=NYF.formatToParts(new Date(ms));const wd=p.find(x=>x.type==='weekday').value,hr=+p.find(x=>x.type==='hour').value%24;
  if(wd==='Sat')return false;if(wd==='Sun')return hr>=18;if(wd==='Fri')return hr<17;return hr!==17;}
// ---------------- helpers ----------------
const fmt=x=>x==null||!isFinite(x)?'—':x.toLocaleString('en-US',{minimumFractionDigits:x>=100?2:4,maximumFractionDigits:x>=100?2:4});
const sgn=x=>(x>0?'+':'')+x;
const thTime=ms=>new Date(ms).toLocaleString('th-TH',{weekday:'short',day:'numeric',month:'short',hour:'2-digit',minute:'2-digit',timeZone:'Asia/Bangkok'});
async function getJSON(u){const r=await fetch(u,{headers:{'user-agent':'trend-analyzer-bot'}});if(!r.ok)throw new Error(u+' → HTTP '+r.status);return r.json();}
async function page(tf,sym,end){let last;
  for(const host of ['https://data-api.binance.vision','https://api.binance.com','https://api1.binance.com']){
    try{return await getJSON(`${host}/api/v3/klines?symbol=${sym}&interval=${tf}&limit=1000${end?'&endTime='+end:''}`);}catch(e){last=e;}}
  throw last;}
// ดึง 3,000 แท่งเหมือนหน้าเว็บ ให้สถิติตรงกัน
async function klines(tf,sym,pages=3){let all=await page(tf,sym);
  for(let p=1;p<pages&&all.length;p++){const more=await page(tf,sym,all[0][0]-1).catch(()=>[]);if(!more.length)break;all=more.concat(all);if(more.length<1000)break;}
  return all.map(k=>({time:Math.floor(k[0]/1000),open:+k[1],high:+k[2],low:+k[3],close:+k[4],closeTime:Math.floor(k[6]/1000)}));}
async function tg(text){if(!CONF.token||!CONF.chat){console.log('[no telegram]\n'+text);return;}
  const r=await fetch(`https://api.telegram.org/bot${CONF.token}/sendMessage`,{method:'POST',headers:{'content-type':'application/json'},body:JSON.stringify({chat_id:CONF.chat,text,disable_web_page_preview:true})});
  const d=await r.json().catch(()=>({}));if(!d.ok)throw new Error('Telegram: '+(d.description||r.status));}
function loadState(){try{return JSON.parse(fs.readFileSync(STATE_FILE,'utf8'));}catch(e){return {};}}
function saveState(st){fs.writeFileSync(STATE_FILE,JSON.stringify(st,null,1)+'\n');}

// ---------------- analysis (เหมือนหน้าเว็บ) ----------------
function analyzeBars(bars,horizon){
  const c=bars.map(b=>b.close),h=bars.map(b=>b.high),l=bars.map(b=>b.low),n=c.length;
  const I={c,e9:ema(c,CFG.f),e21:ema(c,CFG.s),e50:ema(c,CFG.t),r:rsi(c,CFG.r),mh:macd(c,CFG.m)},a=atr(h,l,c);
  const bk={};for(let i=55;i<n-horizon;i++){const s=scoreAt(i,I);if(!s)continue;const b=bk[s.score]||(bk[s.score]={n:0,up:0});b.n++;if(c[i+horizon]>c[i])b.up++;}
  const cur=scoreAt(n-1,I),pr=cur?probFrom(bk,cur.score):null;
  return {I,a,c,h,l,n,cur,pr};}
function htfDir(bars,tSec){const c=bars.map(x=>x.close),e9=ema(c,9),e21=ema(c,21),e50=ema(c,50);let dir=null;
  for(let i=0;i<bars.length;i++){if(bars[i].closeTime+1>tSec)break;dir=e50[i]==null?0:(c[i]>e50[i]&&e9[i]>e21[i])?1:(c[i]<e50[i]&&e9[i]<e21[i])?-1:0;}
  return dir;}
async function newsWindow(){if(CONF.news!=='on')return [];
  try{const d=await getJSON('https://nfs.faireconomy.media/ff_calendar_thisweek.json');const now=Date.now();
    return d.map(e=>({t:Date.parse(e.date),title:e.title,cur:e.country,imp:e.impact,fc:e.forecast,prev:e.previous}))
      .filter(e=>e.cur==='USD'&&e.imp==='High'&&e.t);}catch(e){console.log('calendar error',e.message);return [];}}
function sizeLine(risk,P,size){if(!(CONF.bal>0)||!(risk>0))return '';const riskAcc=CONF.bal*CONF.riskPct/100*size,usd=CONF.cur==='THB'?riskAcc/CONF.fx:riskAcc;
  const m=(CONF.cur==='THB'?'฿':'$')+Math.round(riskAcc).toLocaleString();
  if(isGold)return `ขนาดไม้: ${(usd/(risk*CONF.oz)).toFixed(2)} lot (เสี่ยง ${m})`;
  return `ขนาดไม้: ${(usd/risk).toPrecision(3)} ${SYM.replace('USDT','')} (เสี่ยง ${m})`;}

async function main(){
  const st=loadState();st.open=st.open||[];st.newsSent=st.newsSent||[];
  const raw=await klines(CONF.tf,SYM),nowS=Math.floor(Date.now()/1000);
  const closed=raw.filter(b=>b.closeTime<nowS).map(b=>isGold&&CONF.offset?{...b,open:b.open+CONF.offset,high:b.high+CONF.offset,low:b.low+CONF.offset,close:b.close+CONF.offset}:b);
  const last=closed[closed.length-1],label=`${NAMES[CONF.asset]||CONF.asset} · TF ${CONF.tf}`;
  const msgs=[];
  // 1) ติดตามผลสัญญาณที่เปิดอยู่
  for(const j of st.open){const k=closed.findIndex(b=>b.time>j.bt);if(k<0)continue;
    const pos={side:j.side,i0:0,P:j.P,sl:j.sl,tp1:j.tp1,tp2:j.tp2,risk:j.risk,half:false};let done=null;
    for(let i=k,cnt=1;i<closed.length;i++,cnt++){const r=manageTrade(pos,closed[i].high,closed[i].low,closed[i].close,cnt);if(r){done=r;break;}}
    if(done){j.closed=true;const R=done.R-(j.cost||0);msgs.push(`${R>0?'✅':'❌'} ผลสัญญาณ ${j.side==='LONG'?'ซื้อ':'ขาย'} ${fmt(j.P)}\n${label}\nออก: ${done.why} → ${R>=0?'+':''}${R.toFixed(2)}R`);
      st.stats=st.stats||{n:0,net:0,win:0};st.stats.n++;st.stats.net+=R;if(R>0)st.stats.win++;}
    else if(pos.half&&!j.half){j.half=true;msgs.push(`🎯 ถึง TP1 แล้ว (${fmt(j.tp1)}) ปิดครึ่งไม้ เลื่อน SL มาทุน ${fmt(j.P)}\n${label}`);}}
  st.open=st.open.filter(j=>!j.closed);
  // 2) เตือนข่าวแรงล่วงหน้า 30 นาที
  const events=await newsWindow(),nowMs=Date.now();
  for(const e of events){const dt=e.t-nowMs,key=e.t+e.title;if(dt>0&&dt<=35*60000&&!st.newsSent.includes(key)){st.newsSent.push(key);
    msgs.push(`⚠ ข่าวแรง USD อีก ${Math.round(dt/60000)} นาที\n${e.title}\nเวลา ${thTime(e.t)}${e.fc?'\nคาดการณ์ '+e.fc:''}${e.prev?' · ครั้งก่อน '+e.prev:''}\nบอทจะงดให้สัญญาณช่วงข่าว`);}}
  st.newsSent=st.newsSent.slice(-50);
  // 3) วิเคราะห์เฉพาะเมื่อมีแท่งปิดใหม่
  if(st.lastBar!==last.time){st.lastBar=last.time;
    const A=analyzeBars(closed,CONF.horizon);let side='WAIT',why='';
    if(A.cur&&A.pr){const d=decide(A.cur.score,A.pr.p,A.pr.n,CONF.mode);if(d)side=d;}
    const closeT=last.closeTime+1;
    if(side!=='WAIT'&&CONF.htf!=='off'&&HTF_MAP[CONF.tf]){const hb=await klines(HTF_MAP[CONF.tf],SYM,1),dir=htfDir(hb,closeT),t=side==='LONG'?1:-1;
      if(dir!=null&&(dir===-t||(CONF.htf==='align'&&dir!==t))){why=`สวนเทรนด์ TF ใหญ่ (${HTF_MAP[CONF.tf]})`;side='WAIT';}}
    if(side!=='WAIT'&&isGold&&!goldOpen(closeT*1000)){why='ตลาดทองโลกปิด';side='WAIT';}
    if(side!=='WAIT'&&events.some(e=>e.t>nowMs-15*60000&&e.t<nowMs+30*60000)){why='ช่วงข่าวแรง USD';side='WAIT';}
    let L=null;
    if(side!=='WAIT'){const n=A.n,P=A.c[n-1],Av=A.a[n-1]||P*0.002,lv=levelsAt(A.h,A.l,A.c,n-1,150,3,Av*0.3);L=tradeLevels(side,P,Av,lv.sup,lv.res);
      if(L.tooClose){why=side==='LONG'?'แนวต้านใกล้เกินไป':'แนวรับใกล้เกินไป';side='WAIT';L=null;}}
    console.log(new Date().toISOString(),label,'score',A.cur&&A.cur.score,'pUp',A.pr&&A.pr.p.toFixed(3),'→',side,why);
    if(side!==st.lastSide){
      if(L){const P=A.c[A.n-1],cost=P*(parseFloat(CONF.cost)>=0?parseFloat(CONF.cost):(isGold?0.012:0.1))/100/L.risk;
        msgs.push([`${side==='LONG'?'🟢 ซื้อ (LONG)':'🔴 ขาย (SHORT)'} · ยืนยันแท่งปิดแล้ว`,label,`ราคาปิด ${fmt(P)}`,'',
          `โซนเข้า: ${fmt(L.entryLow)} – ${fmt(L.entryHigh)}`,`Stop Loss: ${fmt(L.sl)}`,`TP1 (ปิดครึ่ง): ${fmt(L.tp1)}`,`TP2: ${fmt(L.tp2)}`,`R:R ≈ 1 : ${L.rr.toFixed(2)}`,
          sizeLine(L.risk,P,1),'',`คะแนน ${sgn(A.cur.score)} · โอกาสขึ้น ${(A.pr.p*100).toFixed(0)}% (จากอดีต ${A.pr.n} ครั้ง)`,
          '(บอทเซิร์ฟเวอร์ · ไม่ใช่คำแนะนำการลงทุน · ตั้ง SL ทุกครั้ง)'].filter(x=>x!==undefined).join('\n'));
        st.open.push({side,bt:last.time,P,sl:L.sl,tp1:L.tp1,tp2:L.tp2,risk:L.risk,cost});st.open=st.open.slice(-20);}
      else if(CONF.sendWait&&(st.lastSide==='LONG'||st.lastSide==='SHORT'))msgs.push(`🟡 สัญญาณกลับเป็นรอ${why?' ('+why+')':''}\n${label}\nราคา ${fmt(A.c[A.n-1])}`);
      st.lastSide=side;}
  }
  for(const m of msgs)await tg(m);
  st.updated=new Date().toISOString();saveState(st);
}
main().catch(e=>{console.error(e);process.exitCode=1;});
