/* チェスエンジン(rookie 1.0 quick-lite)
 * rookie 1.0 quick 系の軽量版。評価キャッシュとポーン構造キャッシュを持ち、
 * 通常評価は Pos が保持する増分値で計算する。evalF の threat / rook 項目は既定オフ。
 * レベル21に変化球 (trapPhase) は無く、探索に全時間を使う。
 * 画面(Index.html の <script src>)と Web Worker(importScripts)の両方から読み込む。
 * 外には globalThis.ChessEngine だけを公開し、内部の定数・関数はグローバルに出さない。
 */
(function(){
'use strict';
const PAWN=1,KNIGHT=2,BISHOP=3,ROOK=4,QUEEN=5,KING=6;
const F_EP=1,F_CK=2,F_CQ=4,F_DP=8;
const START_FEN='rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1';
const INF=32000,MATE=30000,MAXPLY=64;
const VAL=[0,100,320,330,500,900,0];
const PROMO_ALL=[5,4,3,2],PROMO_Q=[5];

/* ---- 盤面は64マスの配列。index = 段*8+筋、段0 = 8段目(黒の後列) ---- */
const KN=[],KG=[],RAYS=[];
(function(){
  const kn=[[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]];
  const kg=[[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]];
  const dirs=[[-1,0],[1,0],[0,-1],[0,1],[-1,-1],[-1,1],[1,-1],[1,1]]; /* 0-3 縦横, 4-7 斜め */
  for(let s=0;s<64;s++){
    const r=s>>3,c=s&7;
    KN[s]=[];KG[s]=[];RAYS[s]=[];
    for(const d of kn){const rr=r+d[0],cc=c+d[1];if(rr>=0&&rr<8&&cc>=0&&cc<8)KN[s].push(rr*8+cc);}
    for(const d of kg){const rr=r+d[0],cc=c+d[1];if(rr>=0&&rr<8&&cc>=0&&cc<8)KG[s].push(rr*8+cc);}
    for(const d of dirs){
      const ray=[];let rr=r+d[0],cc=c+d[1];
      while(rr>=0&&rr<8&&cc>=0&&cc<8){ray.push(rr*8+cc);rr+=d[0];cc+=d[1];}
      RAYS[s].push(ray);
    }
  }
})();

const CMASK=new Uint8Array(64).fill(15);
CMASK[60]=12;CMASK[56]=13;CMASK[63]=14;CMASK[4]=3;CMASK[0]=7;CMASK[7]=11;

/* ---- Zobristハッシュ ---- */
let _seed=0x2545F491;
function rnd32(){_seed=(_seed+0x6D2B79F5)|0;let t=Math.imul(_seed^(_seed>>>15),1|_seed);t=(t+Math.imul(t^(t>>>7),61|t))^t;return (t^(t>>>14))|0;}
const Z1=new Int32Array(13*64),Z2=new Int32Array(13*64);
const ZC1=new Int32Array(16),ZC2=new Int32Array(16),ZE1=new Int32Array(8),ZE2=new Int32Array(8);
for(let i=0;i<Z1.length;i++){Z1[i]=rnd32();Z2[i]=rnd32();}
for(let i=0;i<16;i++){ZC1[i]=rnd32();ZC2[i]=rnd32();}
for(let i=0;i<8;i++){ZE1[i]=rnd32();ZE2[i]=rnd32();}
const ZS1=rnd32(),ZS2=rnd32();

/* ---- 評価用テーブル(白視点、a8→h1の並び) ---- */
const PST=[null,
[0,0,0,0,0,0,0,0, 50,50,50,50,50,50,50,50, 10,10,20,30,30,20,10,10, 5,5,10,25,25,10,5,5, 0,0,0,20,20,0,0,0, 5,-5,-10,0,0,-10,-5,5, 5,10,10,-20,-20,10,10,5, 0,0,0,0,0,0,0,0],
[-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,0,0,0,-20,-40, -30,0,10,15,15,10,0,-30, -30,5,15,20,20,15,5,-30, -30,0,15,20,20,15,0,-30, -30,5,10,15,15,10,5,-30, -40,-20,0,5,5,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50],
[-20,-10,-10,-10,-10,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,10,10,5,0,-10, -10,5,5,10,10,5,5,-10, -10,0,10,10,10,10,0,-10, -10,10,10,10,10,10,10,-10, -10,5,0,0,0,0,5,-10, -20,-10,-10,-10,-10,-10,-10,-20],
[0,0,0,0,0,0,0,0, 5,10,10,10,10,10,10,5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 0,0,0,5,5,0,0,0],
[-20,-10,-10,-5,-5,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,5,5,5,0,-10, -5,0,5,5,5,5,0,-5, 0,0,5,5,5,5,0,-5, -10,5,5,5,5,5,0,-10, -10,0,5,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20]];
const KMG=[-30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -20,-30,-30,-40,-40,-30,-30,-20, -10,-20,-20,-20,-20,-20,-20,-10, 20,20,0,0,0,0,20,20, 20,30,10,0,0,10,30,20];
const KEG=[-50,-40,-30,-20,-20,-30,-40,-50, -30,-20,-10,0,0,-10,-20,-30, -30,-10,20,30,30,20,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,30,40,40,30,-10,-30, -30,-10,20,30,30,20,-10,-30, -30,-30,0,0,0,0,-30,-30, -50,-30,-30,-30,-30,-30,-30,-50];

function mk(from,to,piece,cap,promo,flags){
  return {from:from,to:to,piece:piece,cap:cap,promo:promo,flags:flags,enc:from|(to<<6)|(promo<<12)|(flags<<16),score:0};
}
/* BUG-3: EPをハッシュに含めるのは手番側ポーンが実際にEPマスへ取れる場合だけ */
function epHashable(b,turn,ep){
  if(ep<0)return false;
  const f=ep&7;
  if(turn===1)return (f>0&&b[ep+7]===1)||(f<7&&b[ep+9]===1);
  return (f>0&&b[ep-9]===-1)||(f<7&&b[ep-7]===-1);
}

class Pos{
  constructor(){
    this.b=new Int8Array(64);
    this.turn=1;this.castle=0;this.ep=-1;this.half=0;this.full=1;
    this.kingSq=[60,4];
    this.h1=0;this.h2=0;
    this.ph1=0;this.ph2=0; /* ポーン専用ハッシュ */
    /* 評価の増分値 (通常評価用): 素材+PST合計(白視点), 非ポーン素材, ビショップ数, マイナー数, その他駒数 */
    this.mat=0;this.npm=0;this.bw=0;this.bb=0;this.minors=0;this.others=0;
    this.stack=[];this.hist=[];
  }
  loadFEN(fen){
    /* BUG-4: 非文字列は専用Errorにする */
    if(typeof fen!=='string')throw new Error('Invalid FEN: fen must be a string');
    const parts=fen.trim().split(/\s+/);
    /* BUG-4: 駒配置欄の不正文字はエラー */
    if(!parts[0]||/[^pnbrqkPNBRQK12345678\/]/.test(parts[0]))throw new Error('Invalid FEN: invalid character in piece placement');
    this.b.fill(0);
    this.kingSq=[-1,-1]; /* BUG-1: kingSqは毎回リセット */
    let sq=0,kingsW=0,kingsB=0;
    const rows=parts[0].split('/');
    /* BUG-1: 8段ちょうどを検証 */
    if(rows.length!==8)throw new Error('Invalid FEN: piece placement must have exactly 8 ranks');
    for(let r=0;r<8;r++){
      let fileCount=0;
      for(const ch of rows[r]){
        if(ch>='1'&&ch<='8'){sq+=+ch;fileCount+=+ch;continue;}
        const lower=ch.toLowerCase();
        const type='pnbrqk'.indexOf(lower)+1;
        const color=ch===lower?-1:1;
        /* BUG-1: ポーンが1段目/8段目にある場合は不正 */
        if(type===PAWN&&(r===0||r===7))throw new Error('Invalid FEN: pawn on first or eighth rank');
        if(sq<0||sq>=64)throw new Error('Invalid FEN: piece placement out of board');
        this.b[sq]=type*color;
        if(type===KING){this.kingSq[color===1?0:1]=sq;if(color===1)kingsW++;else kingsB++;}
        sq++;fileCount++;
      }
      /* BUG-1: 各段8マスちょうどを検証 */
      if(fileCount!==8)throw new Error('Invalid FEN: each rank must have exactly 8 squares');
    }
    if(sq!==64)throw new Error('Invalid FEN: piece placement must have exactly 64 squares');
    /* BUG-1: 白黒キング各1つを検証 */
    if(kingsW!==1||kingsB!==1)throw new Error('Invalid FEN: exactly one white king and one black king are required');
    this.turn=parts[1]==='b'?-1:1;
    let c=0;const cs=parts[2]||'-';
    if(cs.indexOf('K')>=0)c|=1;
    if(cs.indexOf('Q')>=0)c|=2;
    if(cs.indexOf('k')>=0)c|=4;
    if(cs.indexOf('q')>=0)c|=8;
    this.castle=c;
    /* BUG-2: EP欄は '-' か /^[a-h][36]$/ のみ受理、それ以外はエラー */
    if(!parts[3]||parts[3]==='-')this.ep=-1;
    else{
      if(!/^[a-h][36]$/.test(parts[3]))throw new Error('Invalid FEN: invalid en passant square');
      this.ep='abcdefgh'.indexOf(parts[3][0])+(8-parseInt(parts[3][1],10))*8;
      /* BUG-2: 取られる側の敵ポーンがEPマスの後ろにいなければ ep=-1 に落とす */
      const behind=parts[3][1]==='6'?this.ep+8:this.ep-8;
      const enemyPawn=parts[3][1]==='6'?-1:1;
      if(this.b[behind]!==enemyPawn)this.ep=-1;
    }
    /* BUG-4: halfは0以上、fullは1以上にクランプ */
    {const h=parseInt(parts[4],10);this.half=Number.isFinite(h)?Math.max(0,h):0;}
    {const f=parseInt(parts[5],10);this.full=Number.isFinite(f)?Math.max(1,f):1;}
    this.stack=[];
    this.computeHash();
    this.hist=[this.h1];
  }
  computeHash(){
    let h1=0,h2=0,ph1=0,ph2=0;
    for(let s=0;s<64;s++){
      const p=this.b[s];
      if(p){const i=(p+6)*64+s;h1^=Z1[i];h2^=Z2[i];if(p===PAWN||p===-PAWN){ph1^=Z1[i];ph2^=Z2[i];}}
    }
    this.ph1=ph1;this.ph2=ph2;
    let mat=0,npm=0,bw=0,bb=0,minors=0,others=0;
    for(let s=0;s<64;s++){
      const p=this.b[s];
      if(!p)continue;
      const t=p>0?p:-p;
      if(t===KING)continue;
      if(t===PAWN)others++;
      else{
        npm+=VAL[t];
        if(t===KNIGHT||t===BISHOP)minors++;else others++;
      }
      if(p>0){mat+=VAL[t]+PST[t][s];if(t===BISHOP)bw++;}
      else{mat-=VAL[t]+PST[t][s^56];if(t===BISHOP)bb++;}
    }
    this.mat=mat;this.npm=npm;this.bw=bw;this.bb=bb;this.minors=minors;this.others=others;
    if(this.turn===-1){h1^=ZS1;h2^=ZS2;}
    h1^=ZC1[this.castle];h2^=ZC2[this.castle];
    if(epHashable(this.b,this.turn,this.ep)){h1^=ZE1[this.ep&7];h2^=ZE2[this.ep&7];} /* BUG-3 */
    this.h1=h1;this.h2=h2;
  }
  /* sq が by 側の駒に攻撃されているか */
  attacked(sq,by){
    const b=this.b,r=sq>>3,c=sq&7;
    const pr=by===1?r+1:r-1;
    if(pr>=0&&pr<8){
      if(c>0&&b[pr*8+c-1]===by)return true;
      if(c<7&&b[pr*8+c+1]===by)return true;
    }
    const kn=KN[sq];
    for(let i=0;i<kn.length;i++)if(b[kn[i]]===by*2)return true;
    const kg=KG[sq];
    for(let i=0;i<kg.length;i++)if(b[kg[i]]===by*6)return true;
    const rays=RAYS[sq];
    for(let d=0;d<8;d++){
      const ray=rays[d];
      for(let i=0;i<ray.length;i++){
        const p=b[ray[i]];
        if(p!==0){
          if(p===by*5||p===by*(d<4?4:3))return true;
          break;
        }
      }
    }
    return false;
  }
  inCheck(){return this.attacked(this.kingSq[this.turn===1?0:1],-this.turn);}
  /* make() の直後に呼ぶ。直前に指した側のキングが取られる形になっていないか */
  illegal(){return this.attacked(this.kingSq[this.turn===1?1:0],this.turn);}

  /* 疑似合法手の生成。caps=true なら駒取り+クイーン昇格のみ */
  gen(caps){
    const b=this.b,us=this.turn,moves=[];
    for(let s=0;s<64;s++){
      const p=b[s];
      if(p*us<=0)continue;
      const t=p*us;
      if(t===PAWN){
        const dir=us===1?-8:8,r=s>>3,c=s&7;
        const promoRow=us===1?1:6,startRow=us===1?6:1;
        const promos=caps?PROMO_Q:PROMO_ALL;
        const f=s+dir;
        if(b[f]===0){
          if(r===promoRow){for(let i=0;i<promos.length;i++)moves.push(mk(s,f,p,0,promos[i],0));}
          else if(!caps){
            moves.push(mk(s,f,p,0,0,0));
            if(r===startRow&&b[f+dir]===0)moves.push(mk(s,f+dir,p,0,0,F_DP));
          }
        }
        for(let k=-1;k<=1;k+=2){
          const cc=c+k;
          if(cc<0||cc>7)continue;
          const to=f+k,q=b[to];
          if(q*us<0){
            if(r===promoRow){for(let i=0;i<promos.length;i++)moves.push(mk(s,to,p,q,promos[i],0));}
            else moves.push(mk(s,to,p,q,0,0));
          }else if(q===0&&to===this.ep&&b[to+(us===1?8:-8)]===-us*PAWN){ /* BUG-2: 敵ポーン存在を条件に二重防御 */
            moves.push(mk(s,to,p,-us*PAWN,0,F_EP));
          }
        }
      }else if(t===KNIGHT||t===KING){
        const list=t===KNIGHT?KN[s]:KG[s];
        for(let i=0;i<list.length;i++){
          const to=list[i],q=b[to];
          if(q===0){if(!caps)moves.push(mk(s,to,p,0,0,0));}
          else if(q*us<0)moves.push(mk(s,to,p,q,0,0));
        }
        if(t===KING&&!caps){
          if(us===1&&s===60){
            if((this.castle&1)&&b[61]===0&&b[62]===0&&b[63]===4&&!this.attacked(60,-1)&&!this.attacked(61,-1)&&!this.attacked(62,-1))moves.push(mk(60,62,p,0,0,F_CK));
            if((this.castle&2)&&b[59]===0&&b[58]===0&&b[57]===0&&b[56]===4&&!this.attacked(60,-1)&&!this.attacked(59,-1)&&!this.attacked(58,-1))moves.push(mk(60,58,p,0,0,F_CQ));
          }else if(us===-1&&s===4){
            if((this.castle&4)&&b[5]===0&&b[6]===0&&b[7]===-4&&!this.attacked(4,1)&&!this.attacked(5,1)&&!this.attacked(6,1))moves.push(mk(4,6,p,0,0,F_CK));
            if((this.castle&8)&&b[3]===0&&b[2]===0&&b[1]===0&&b[0]===-4&&!this.attacked(4,1)&&!this.attacked(3,1)&&!this.attacked(2,1))moves.push(mk(4,2,p,0,0,F_CQ));
          }
        }
      }else{
        const d0=t===BISHOP?4:0,d1=t===ROOK?4:8;
        const rays=RAYS[s];
        for(let d=d0;d<d1;d++){
          const ray=rays[d];
          for(let i=0;i<ray.length;i++){
            const to=ray[i],q=b[to];
            if(q===0){if(!caps)moves.push(mk(s,to,p,0,0,0));}
            else{if(q*us<0)moves.push(mk(s,to,p,q,0,0));break;}
          }
        }
      }
    }
    return moves;
  }

  make(m){
    const b=this.b,us=this.turn,from=m.from,to=m.to,p=m.piece;
    let h1=this.h1,h2=this.h2,i;
    const u={castle:this.castle,ep:this.ep,half:this.half,h1:h1,h2:h2,ph1:this.ph1,ph2:this.ph2,cap:0,mat:this.mat,npm:this.npm,bw:this.bw,bb:this.bb,minors:this.minors,others:this.others};
    let ph1=this.ph1,ph2=this.ph2;
    h1^=ZC1[this.castle];h2^=ZC2[this.castle];
    if(epHashable(b,us,this.ep)){h1^=ZE1[this.ep&7];h2^=ZE2[this.ep&7];} /* BUG-3: 指す前で判定しcomputeHashと一致 */
    i=(p+6)*64+from;h1^=Z1[i];h2^=Z2[i];
    if(p===us*PAWN){ph1^=Z1[i];ph2^=Z2[i];}
    b[from]=0;
    let cap;
    if(m.flags&F_EP){
      const cs=to+(us===1?8:-8);
      cap=b[cs];b[cs]=0;
      i=(cap+6)*64+cs;h1^=Z1[i];h2^=Z2[i];
      ph1^=Z1[i];ph2^=Z2[i]; /* EPで取られる駒はポーン */
    }else{
      cap=b[to];
      if(cap){i=(cap+6)*64+to;h1^=Z1[i];h2^=Z2[i];if(cap===PAWN||cap===-PAWN){ph1^=Z1[i];ph2^=Z2[i];}}
    }
    u.cap=cap;m.cap=cap;
    const placed=m.promo?m.promo*us:p;
    /* 評価増分値の更新: 動いた駒・取られた駒・成った駒の寄与を付け替える */
    {
      const pt=p>0?p:-p;
      if(pt!==KING)this.mat-=us>0?VAL[pt]+PST[pt][from]:-(VAL[pt]+PST[pt][from^56]);
      if(cap){
        const ct=cap>0?cap:-cap,csq=(m.flags&F_EP)?to+(us===1?8:-8):to;
        if(ct!==KING){
          this.mat-=cap>0?VAL[ct]+PST[ct][csq]:-(VAL[ct]+PST[ct][csq^56]);
          if(ct===PAWN)this.others--;
          else{
            this.npm-=VAL[ct];
            if(ct===KNIGHT||ct===BISHOP){this.minors--;if(ct===BISHOP){if(cap>0)this.bw--;else this.bb--;}}
            else this.others--;
          }
        }
      }
      const lt=placed>0?placed:-placed;
      if(lt!==KING){
        this.mat+=us>0?VAL[lt]+PST[lt][to]:-(VAL[lt]+PST[lt][to^56]);
        if(m.promo){
          /* ポーンが駒になった: カウント区分を付け替える */
          this.others--;
          this.npm+=VAL[lt];
          if(lt===KNIGHT||lt===BISHOP){this.minors++;if(lt===BISHOP){if(us>0)this.bw++;else this.bb++;}}
          else this.others++;
        }
      }
    }
    b[to]=placed;
    i=(placed+6)*64+to;h1^=Z1[i];h2^=Z2[i];
    if(placed===us*PAWN){ph1^=Z1[i];ph2^=Z2[i];}
    if(m.flags&(F_CK|F_CQ)){
      const rf=(m.flags&F_CK)?to+1:to-2;
      const rt=(m.flags&F_CK)?to-1:to+1;
      const rook=b[rf];
      this.mat-=us>0?VAL[ROOK]+PST[ROOK][rf]:-(VAL[ROOK]+PST[ROOK][rf^56]);
      this.mat+=us>0?VAL[ROOK]+PST[ROOK][rt]:-(VAL[ROOK]+PST[ROOK][rt^56]);
      b[rf]=0;b[rt]=rook;
      i=(rook+6)*64+rf;h1^=Z1[i];h2^=Z2[i];
      i=(rook+6)*64+rt;h1^=Z1[i];h2^=Z2[i];
    }
    if(p===us*KING)this.kingSq[us===1?0:1]=to;
    this.castle&=CMASK[from]&CMASK[to];
    this.ep=(m.flags&F_DP)?((from+to)>>1):-1;
    if(p===us*PAWN||cap)this.half=0;else this.half++;
    if(us===-1)this.full++;
    this.turn=-us;
    h1^=ZS1;h2^=ZS2;
    h1^=ZC1[this.castle];h2^=ZC2[this.castle];
    if(epHashable(b,this.turn,this.ep)){h1^=ZE1[this.ep&7];h2^=ZE2[this.ep&7];} /* BUG-3: 指した後の手番・盤面で判定 */
    this.h1=h1;this.h2=h2;this.ph1=ph1;this.ph2=ph2;
    this.stack.push(u);this.hist.push(h1);
  }
  unmake(m){
    const u=this.stack.pop();this.hist.pop();
    const b=this.b,us=-this.turn,from=m.from,to=m.to;
    this.turn=us;
    b[from]=m.piece;
    if(m.flags&F_EP){b[to]=0;b[to+(us===1?8:-8)]=u.cap;}
    else b[to]=u.cap;
    if(m.flags&(F_CK|F_CQ)){
      const rf=(m.flags&F_CK)?to+1:to-2;
      const rt=(m.flags&F_CK)?to-1:to+1;
      b[rf]=b[rt];b[rt]=0;
    }
    if(m.piece===us*KING)this.kingSq[us===1?0:1]=from;
    this.castle=u.castle;this.ep=u.ep;this.half=u.half;this.h1=u.h1;this.h2=u.h2;this.ph1=u.ph1;this.ph2=u.ph2;
    this.mat=u.mat;this.npm=u.npm;this.bw=u.bw;this.bb=u.bb;this.minors=u.minors;this.others=u.others;
    if(us===-1)this.full--;
  }
  legalMoves(){
    const out=[],ms=this.gen(false);
    for(let i=0;i<ms.length;i++){
      const m=ms[i];
      this.make(m);
      if(!this.illegal())out.push(m);
      this.unmake(m);
    }
    return out;
  }
  hasLegalMove(){
    const ms=this.gen(false);
    for(let i=0;i<ms.length;i++){
      const m=ms[i];
      this.make(m);
      const ok=!this.illegal();
      this.unmake(m);
      if(ok)return true;
    }
    return false;
  }
  /* 同一局面が(同じ手番で)何回現れたか。現局面を含む */
  repCount(){
    let n=1;const len=this.hist.length;
    const lim=Math.max(0,len-1-this.half);
    for(let i=len-3;i>=lim;i-=2)if(this.hist[i]===this.h1)n++;
    return n;
  }
  isRepetition(){
    const len=this.hist.length;
    const lim=Math.max(0,len-1-this.half);
    for(let i=len-3;i>=lim;i-=2)if(this.hist[i]===this.h1)return true;
    return false;
  }
  /* 「パス」の手(ヌルムーブ)。探索の枝刈り専用で、実戦では指さない */
  makeNull(){
    const u={castle:this.castle,ep:this.ep,half:this.half,h1:this.h1,h2:this.h2,cap:0};
    let h1=this.h1,h2=this.h2;
    if(epHashable(this.b,this.turn,this.ep)){h1^=ZE1[this.ep&7];h2^=ZE2[this.ep&7];} /* BUG-3 */
    h1^=ZS1;h2^=ZS2;
    this.ep=-1;this.turn=-this.turn;this.half++;
    this.h1=h1;this.h2=h2;
    this.stack.push(u);this.hist.push(h1);
  }
  unmakeNull(){
    const u=this.stack.pop();this.hist.pop();
    this.turn=-this.turn;this.ep=u.ep;this.half=u.half;this.h1=u.h1;this.h2=u.h2;
  }
  /* us 側にポーン・キング以外の駒があるか(ヌルムーブが危険な終盤の見分け用) */
  hasPieces(us){
    for(let s=0;s<64;s++){const t=this.b[s]*us;if(t>1&&t<6)return true;}
    return false;
  }
  /* キングのみ / キング+マイナーピース1枚 は引き分け */
  insufficient(){
    let minors=0,knights=0,bc=-1,allSame=true;
    for(let s=0;s<64;s++){
      const v=this.b[s],t=Math.abs(v);
      if(t===PAWN||t===ROOK||t===QUEEN)return false;
      if(t===KNIGHT||t===BISHOP)minors++;
      if(t===KNIGHT)knights++;
      if(t===BISHOP){const c=((s>>3)+(s&7))&1;if(bc<0)bc=c;else if(bc!==c)allSame=false;}
    }
    /* ナイト無しでビショップだけ全て同じ色マスなら、どちらも詰ませられない(デッドポジション) */
    return minors<=1||(minors>=2&&knights===0&&allSame);
  }
}

function perft(pos,d){
  if(d<=0)return 1; /* BUG-5: 負数・小数でもRangeErrorにしない */
  let n=0;
  const ms=pos.gen(false);
  for(let i=0;i<ms.length;i++){
    const m=ms[i];
    pos.make(m);
    if(!pos.illegal())n+=perft(pos,d-1);
    pos.unmake(m);
  }
  return n;
}

/* ---- 棋譜表記(SAN)。指す前の局面で呼ぶ ---- */
function toSAN(pos,m){
  const files='abcdefgh';
  const sqn=function(s){return files[s&7]+(8-(s>>3));};
  const t=Math.abs(m.piece);
  let s;
  if(m.flags&F_CK)s='O-O';
  else if(m.flags&F_CQ)s='O-O-O';
  else{
    const cap=m.cap!==0;
    if(t===PAWN){
      s=cap?files[m.from&7]+'x'+sqn(m.to):sqn(m.to);
      if(m.promo)s+='='+'NBRQ'[m.promo-2];
    }else{
      s='NBRQK'[t-2];
      const others=pos.legalMoves().filter(function(o){return o.to===m.to&&o.piece===m.piece&&o.from!==m.from;});
      if(others.length){
        const sameFile=others.some(function(o){return (o.from&7)===(m.from&7);});
        const sameRank=others.some(function(o){return (o.from>>3)===(m.from>>3);});
        if(!sameFile)s+=files[m.from&7];
        else if(!sameRank)s+=String(8-(m.from>>3));
        else s+=sqn(m.from);
      }
      if(cap)s+='x';
      s+=sqn(m.to);
    }
  }
  pos.make(m);
  if(pos.inCheck())s+=pos.hasLegalMove()?'+':'#';
  pos.unmake(m);
  return s;
}

/* 対称丸め(ties-to-even)。Math.round は x.5 で +∞ 側に寄るため
   ミラー局面で評価が ±1cp ずれる非対称が稀に発生する。round(-x)==-round(x) を保証する */
function rint(x){
  const f=Math.floor(x),d=x-f;
  if(d>0.5)return f+1;
  if(d<0.5)return f;
  return (f&1)?f+1:f;
}

/* ---- 評価関数(手番側から見た点数) ---- */
function evaluate(pos){
  if(SR.fast&&EV.on)return evalF(pos);
  if(pos.others===0&&pos.minors<=1)return 0;
  let sc=pos.mat;
  const ph=Math.min(1,pos.npm/4000);
  const kw=pos.kingSq[0],kb=pos.kingSq[1]^56;
  sc+=(KMG[kw]*ph+KEG[kw]*(1-ph))-(KMG[kb]*ph+KEG[kb]*(1-ph));
  if(pos.bw>=2)sc+=30;
  if(pos.bb>=2)sc-=30;
  sc=rint(sc);
  return pos.turn===1?sc:-sc;
}

/* ---- 拡張評価関数(レベル???用) ----
   駒の価値と配置表に加えて、形勢の良し悪しを決める次の項目を見る。EV は各項目のオン/オフ(検証用)。
   pawn   : ポーン構造(孤立・二重・遅れたポーン・連結/守られたポーン)
   passed : 通過ポーン(進むほど大きな加点。止められていると減点、終盤はキングの距離も見る)
   outpost: ナイトの拠点(敵ポーンに追い払われない前進したマスで、味方ポーンが支えている)
   rook   : ルークの開いた筋/半開きの筋、7段目のルーク
   mob    : 駒の動きやすさ(相手ポーンに取られるマスは数えない)
   king   : キングの安全(ポーンの盾、キング周りへの攻撃の集中)
   threat : ポーンに攻撃されている駒の減点
   tempo  : 手番の加点 */
const EV={on:1,pawn:1,passed:1,outpost:1,rook:0,mob:1,king:1,threat:0,tempo:1};
/* キャッシュのオン/オフ (検証用) */
const CFG={evalCache:1,pawnHash:1};
const PASS_MG=[0,0,6,12,24,44,72,0],PASS_EG=[0,6,14,30,56,96,150,0];
const PCONN=[0,0,4,6,9,16,24,0];
const PKRW=[0,0,0,1,1,2,3,0];
const THREAT=[0,0,12,12,20,30,0];
const ATK_W=[0,0,20,20,40,80,0];
const ATK_FAC=[0,0,55,75,88,94,98,100,100];
const wAtt=new Uint8Array(64),bAtt=new Uint8Array(64),zW=new Uint8Array(64),zB=new Uint8Array(64);
const wCnt=new Int8Array(10),bCnt=new Int8Array(10),wMax=new Int8Array(10),bMin=new Int8Array(10);
const wpSq=new Int8Array(16),bpSq=new Int8Array(16),pcSq=new Int8Array(64);
function kdist(a,f){
  const dr=(a>>3)-(f>>3),dc=(a&7)-(f&7);
  return Math.max(dr<0?-dr:dr,dc<0?-dc:dc);
}
/* ポーン構造キャッシュ: ポーン配置だけで決まる評価分 (mg/eg, 白視点) を引く */
const PH_MASK=(1<<14)-1;
const PHlock=new Int32Array(PH_MASK+1),PHmg=new Int32Array(PH_MASK+1),PHeg=new Int32Array(PH_MASK+1);
const PHok=new Uint8Array(PH_MASK+1);
function evalF(pos){
  const b=pos.b;
  let sc=0,npm=0,bw=0,bb=0,minors=0,others=0,mg=0,eg=0;
  wAtt.fill(0);bAtt.fill(0);zW.fill(0);zB.fill(0);
  wCnt.fill(0);bCnt.fill(0);wMax.fill(-1);bMin.fill(8);
  let nw=0,nb=0,np=0,qW=0,qB=0;
  for(let s=0;s<64;s++){
    const p=b[s];
    if(p===0)continue;
    const t=p>0?p:-p;
    if(t===KING)continue;
    if(t===PAWN){
      others++;
      const r=s>>3,c=s&7;
      if(p>0){
        sc+=100+PST[1][s];wpSq[nw++]=s;wCnt[c+1]++;if(r>wMax[c+1])wMax[c+1]=r;
        if(r>0){if(c>0)wAtt[s-9]=1;if(c<7)wAtt[s-7]=1;}
      }else{
        sc-=100+PST[1][s^56];bpSq[nb++]=s;bCnt[c+1]++;if(r<bMin[c+1])bMin[c+1]=r;
        if(r<7){if(c>0)bAtt[s+7]=1;if(c<7)bAtt[s+9]=1;}
      }
      continue;
    }
    npm+=VAL[t];
    if(t===KNIGHT||t===BISHOP)minors++;else others++;
    pcSq[np++]=s;
    if(p>0){sc+=VAL[t]+PST[t][s];if(t===BISHOP)bw++;if(t===QUEEN)qW++;}
    else{sc-=VAL[t]+PST[t][s^56];if(t===BISHOP)bb++;if(t===QUEEN)qB++;}
  }
  if(others===0&&minors<=1)return 0;
  if(LZon){const st=pos.turn===1?sc:-sc;if(st+LZM<=LZa||st-LZM>=LZb){LZhit=true;return st;}}
  const ph=Math.min(1,npm/4000);
  const kwSq=pos.kingSq[0],kbSq=pos.kingSq[1];
  const kw=kwSq,kb=kbSq^56;

  /* ポーン構造と通過ポーン: ポーン配置だけで決まる分はポーン構造キャッシュで引く。
     通過ポーンの「前のマスの占有」と「キング距離」の調整はポーン以外に依存するので外で足す */
  if(EV.pawn||EV.passed){
    const usePH=CFG.pawnHash;
    const phk=usePH?(pos.ph1&PH_MASK):0;
    const phLock=usePH?(pos.ph2^((EV.pawn?0x2545F491:0)^(EV.passed?0x6D2B79F5:0))):0;
    let phHit=false;
    if(usePH&&PHok[phk]&&PHlock[phk]===phLock){mg+=PHmg[phk];eg+=PHeg[phk];phHit=true;}
    if(!phHit){
      let pmg=0,peg=0;
      for(let i=0;i<nw;i++){
        const s=wpSq[i],r=s>>3,c=s&7,rr=7-r,cc=c+1;
        const iso=wCnt[cc-1]===0&&wCnt[cc+1]===0;
        const sup=(c>0&&b[s+7]===1)||(c<7&&b[s+9]===1);
        const pass=bMin[cc-1]>=r&&bMin[cc]>=r&&bMin[cc+1]>=r;
        if(EV.pawn){
          if(iso){pmg-=10;peg-=16;if(bCnt[cc]===0)pmg-=6;}
          else if(!sup&&!pass&&wMax[cc-1]<r&&wMax[cc+1]<r&&r>0&&bAtt[s-8]){pmg-=8;peg-=10;}
          if(sup||(c>0&&b[s-1]===1)||(c<7&&b[s+1]===1)){pmg+=PCONN[rr];peg+=PCONN[rr];}
        }
        if(EV.passed&&pass){pmg+=PASS_MG[rr];peg+=PASS_EG[rr];}
      }
      for(let i=0;i<nb;i++){
        const s=bpSq[i],r=s>>3,c=s&7,rr=r,cc=c+1;
        const iso=bCnt[cc-1]===0&&bCnt[cc+1]===0;
        const sup=(c>0&&b[s-9]===-1)||(c<7&&b[s-7]===-1);
        const pass=wMax[cc-1]<=r&&wMax[cc]<=r&&wMax[cc+1]<=r;
        if(EV.pawn){
          if(iso){pmg+=10;peg+=16;if(wCnt[cc]===0)pmg+=6;}
          else if(!sup&&!pass&&bMin[cc-1]>r&&bMin[cc+1]>r&&r<7&&wAtt[s+8]){pmg+=8;peg+=10;}
          if(sup||(c>0&&b[s-1]===-1)||(c<7&&b[s+1]===-1)){pmg-=PCONN[rr];peg-=PCONN[rr];}
        }
        if(EV.passed&&pass){pmg-=PASS_MG[rr];peg-=PASS_EG[rr];}
      }
      if(EV.pawn){
        for(let f=1;f<=8;f++){
          if(wCnt[f]>1){pmg-=(wCnt[f]-1)*8;peg-=(wCnt[f]-1)*16;}
          if(bCnt[f]>1){pmg+=(bCnt[f]-1)*8;peg+=(bCnt[f]-1)*16;}
        }
      }
      mg+=pmg;eg+=peg;
      if(usePH){PHok[phk]=1;PHlock[phk]=phLock;PHmg[phk]=pmg;PHeg[phk]=peg;}
    }
    if(EV.passed){
      for(let i=0;i<nw;i++){
        const s=wpSq[i],r=s>>3,c=s&7,rr=7-r,cc=c+1;
        if(r>0&&bMin[cc-1]>=r&&bMin[cc]>=r&&bMin[cc+1]>=r){
          const fr=s-8,pm=PASS_MG[rr],pe=PASS_EG[rr];
          if(b[fr]!==0){mg-=(pm-(pm>>1));eg-=(pe-((pe*2/3)|0));}
          if(rr>=3)eg+=(4*kdist(kbSq,fr)-2*kdist(kwSq,fr))*PKRW[rr];
        }
      }
      for(let i=0;i<nb;i++){
        const s=bpSq[i],r=s>>3,c=s&7,rr=r,cc=c+1;
        if(r<7&&wMax[cc-1]<=r&&wMax[cc]<=r&&wMax[cc+1]<=r){
          const fr=s+8,pm=PASS_MG[rr],pe=PASS_EG[rr];
          if(b[fr]!==0){mg+=(pm-(pm>>1));eg+=(pe-((pe*2/3)|0));}
          if(rr>=3)eg-=(4*kdist(kwSq,fr)-2*kdist(kbSq,fr))*PKRW[rr];
        }
      }
    }
  }

  /* 駒の動きやすさ・拠点・ルークの筋・キングへの攻撃 */
  let aUw=0,aNw=0,aUb=0,aNb=0;
  if(EV.king){
    zW[kwSq]=1;zB[kbSq]=1;
    const gw=KG[kwSq],gb=KG[kbSq];
    for(let i=0;i<gw.length;i++)zW[gw[i]]=1;
    for(let i=0;i<gb.length;i++)zB[gb[i]]=1;
  }
  const doScan=EV.mob||EV.king;
  for(let i=0;i<np;i++){
    const s=pcSq[i],p=b[s],white=p>0,t=white?p:-p;
    const r=s>>3,c=s&7,cc=c+1;
    let m1=0,e1=0;
    if(doScan){
      const eAtt=white?bAtt:wAtt,zE=white?zB:zW;
      let cnt=0,hit=0;
      if(t===KNIGHT){
        const a=KN[s];
        for(let k=0;k<a.length;k++){
          const to=a[k];
          if(zE[to])hit=1;
          const q=b[to];
          if(q!==0&&(q>0)===white)continue;
          if(!eAtt[to])cnt++;
        }
      }else{
        const rays=RAYS[s];
        const d0=t===BISHOP?4:0,d1=t===ROOK?4:8;
        for(let d=d0;d<d1;d++){
          const ray=rays[d];
          for(let k=0;k<ray.length;k++){
            const to=ray[k];
            if(zE[to])hit=1;
            const q=b[to];
            if(q===0){if(!eAtt[to])cnt++;continue;}
            if((q>0)!==white&&!eAtt[to])cnt++;
            break;
          }
        }
      }
      if(EV.mob){
        if(t===KNIGHT){m1+=(cnt-4)*4;e1+=(cnt-4)*4;}
        else if(t===BISHOP){m1+=(cnt-6)*5;e1+=(cnt-6)*5;}
        else if(t===ROOK){m1+=(cnt-7)*2;e1+=(cnt-7)*4;}
        else{m1+=cnt-13;e1+=(cnt-13)*2;}
      }
      if(hit){if(white){aNw++;aUw+=ATK_W[t];}else{aNb++;aUb+=ATK_W[t];}}
    }
    if(EV.outpost&&t===KNIGHT&&c>=1&&c<=6){
      if(white){
        const rr=7-r;
        if(rr>=3&&rr<=5&&bMin[cc-1]>=r&&bMin[cc+1]>=r){
          if((c>0&&b[s+7]===1)||(c<7&&b[s+9]===1)){m1+=22;e1+=16;}else{m1+=8;e1+=6;}
        }
      }else if(r>=3&&r<=5&&wMax[cc-1]<=r&&wMax[cc+1]<=r){
        if((c>0&&b[s-9]===-1)||(c<7&&b[s-7]===-1)){m1+=22;e1+=16;}else{m1+=8;e1+=6;}
      }
    }
    if(EV.rook&&t===ROOK){
      const own=white?wCnt[cc]:bCnt[cc],opp=white?bCnt[cc]:wCnt[cc];
      if(own===0){
        if(opp===0){m1+=22;e1+=12;}else{m1+=10;e1+=6;}
      }
      if(white?(r===1&&(kbSq>>3)===0):(r===6&&(kwSq>>3)===7)){m1+=14;e1+=22;}
    }
    if(white){mg+=m1;eg+=e1;}else{mg-=m1;eg-=e1;}
    if(EV.threat&&(white?bAtt[s]:wAtt[s])){
      if(white)sc-=THREAT[t];else sc+=THREAT[t];
    }
  }

  if(EV.king){
    if(aNw>=2){let pen=(aUw*ATK_FAC[aNw>8?8:aNw]/100)|0;if(qW===0)pen>>=1;mg+=pen;}
    if(aNb>=2){let pen=(aUb*ATK_FAC[aNb>8?8:aNb]/100)|0;if(qB===0)pen>>=1;mg-=pen;}
    /* ポーンの盾(キングが自陣の1〜2段目にいるときだけ) */
    const kwr=kwSq>>3,kwc=kwSq&7;
    if(kwr>=6){
      for(let f=(kwc>0?kwc-1:0);f<=(kwc<7?kwc+1:7);f++){
        if(b[(kwr-1)*8+f]===1)mg+=12;
        else if(kwr>=2&&b[(kwr-2)*8+f]===1)mg+=6;
        else{mg-=14;if(wCnt[f+1]===0){mg-=6;if(bCnt[f+1]===0)mg-=6;}}
      }
    }
    const kbr=kbSq>>3,kbc=kbSq&7;
    if(kbr<=1){
      for(let f=(kbc>0?kbc-1:0);f<=(kbc<7?kbc+1:7);f++){
        if(b[(kbr+1)*8+f]===-1)mg-=12;
        else if(kbr<=5&&b[(kbr+2)*8+f]===-1)mg-=6;
        else{mg+=14;if(bCnt[f+1]===0){mg+=6;if(wCnt[f+1]===0)mg+=6;}}
      }
    }
  }

  sc+=rint(mg*ph+eg*(1-ph));
  sc+=(KMG[kw]*ph+KEG[kw]*(1-ph))-(KMG[kb]*ph+KEG[kb]*(1-ph));
  if(bw>=2)sc+=30;
  if(bb>=2)sc-=30;
  sc=rint(sc);
  const stm=pos.turn===1?sc:-sc;
  return EV.tempo?stm+8:stm;
}

/* ---- 探索 ---- */
/* 置換表の大きさは可変(長く考えるレベルほど大きくして、読んだ結果を捨てにくくする) */
let TT_BITS=0,TT_MASK=0;
let TTlock=null,TTscore=null,TTdepth=null,TTflag=null,TTmove=null,TTage=null;
function ensureTT(bits){
  if(TTlock&&TT_BITS===bits)return;
  TT_BITS=bits;TT_MASK=(1<<bits)-1;
  const n=1<<bits;
  TTlock=new Int32Array(n);TTscore=new Int32Array(n);
  TTdepth=new Int8Array(n);TTflag=new Int8Array(n);TTmove=new Int32Array(n);TTage=new Uint8Array(n);
}
const SR={ex:false,gen:0,ev:null,nodes:0,stop:false,deadline:0,start:0,budget:0,total:0,useQ:false,ext:false,lmr:false,nmp:false,noNullAt:-1,depthDone:0,bestScore:0,fast:false,cur:null,killers:[],history:new Int32Array(13*64)};
const LAST={depth:0,trap:false,nodes:0,time:0,score:0};

/* to のマスを、piece を動かす側の敵ポーンが守っているか(安い駒で取られる=損な取りの目安) */
function pawnGuards(pos,to,piece){
  const by=piece>0?-1:1,r=to>>3,c=to&7,pr=by===1?r+1:r-1;
  if(pr<0||pr>7)return false;
  const b=pos.b;
  return (c>0&&b[pr*8+c-1]===by)||(c<7&&b[pr*8+c+1]===by);
}
function scoreMove(m,ttEnc,kl){
  if(m.enc===ttEnc)return 1000000;
  if(m.cap){
    const ac=m.cap<0?-m.cap:m.cap,ap=m.piece<0?-m.piece:m.piece;
    /* 高速探索: ポーンに守られたマスへ高い駒で取りに行く手は、キラー手より後ろに回す */
    if(SR.fast&&FO.bad&&!m.promo&&VAL[ac]<VAL[ap]&&pawnGuards(SR.cur,m.to,m.piece))return 3000+VAL[ac]*10-ap;
    return 10000+VAL[ac]*10-ap+(m.promo?VAL[m.promo]:0);
  }
  if(m.promo)return 9500+VAL[m.promo];
  if(kl){if(m.enc===kl[0])return 9000;if(m.enc===kl[1])return 8900;}
  const h=SR.history[(m.piece+6)*64+m.to];
  if(SR.fast)return h<0?0:(h>7000?7000:h);
  return h;
}
function byScore(a,b){return b.score-a.score;}
/* 高速探索用: 全部を並べ替えず、次に読む手だけを先頭に持ってくる(早く枝刈りされる探索では並べ替えの無駄が大きい) */
function pickNext(moves,i){
  let b=i,bs=moves[i].score;
  for(let j=i+1;j<moves.length;j++){if(moves[j].score>bs){bs=moves[j].score;b=j;}}
  if(b!==i){const t=moves[i];moves[i]=moves[b];moves[b]=t;}
}

/* ---- 強化版の追加部品 ----
   evalX : 評価値の使い回し(同じ局面を何度も詳しく評価しない)。静止探索では、駒の価値と配置だけで
           窓の遥か外とわかる局面は、詳しい項目を省く(LZM は省く目安の差)
   quiesceChk : 静止探索の途中で王手がかかっている局面は「何もしない」評価が使えないので、全ての受けを読む */
const EV_MASK=(1<<17)-1;
/* EVフラグの組み合わせを評価キャッシュのロックに混ぜる (フラグ変更で古い値を使わない) */
const EVK=[0x27D4EB2D,0x165667B1,0x1B56C4E9,0x85EBCA6B,0xC2B2AE35,0x27D4EB2F,0x165667B5,0x9E3779B1,0x85EBCA77];
const EVFLAGS=['on','pawn','passed','outpost','rook','mob','king','threat','tempo'];
function evMix(){let k=0;for(let i=0;i<EVFLAGS.length;i++)if(EV[EVFLAGS[i]])k^=EVK[i];return k;}
const EVlock=new Int32Array(EV_MASK+1),EVval=new Int32Array(EV_MASK+1);
let LZon=false,LZa=0,LZb=0,LZhit=false;
const LZM=350;
function evalX(pos,lazy,a,b){
  const k=pos.h1&EV_MASK,lk=(pos.h2^evMix())|1;
  if(CFG.evalCache&&EVlock[k]===lk)return EVval[k];
  if(lazy){LZon=true;LZa=a;LZb=b;LZhit=false;}
  const v=evaluate(pos);
  LZon=false;
  if(CFG.evalCache&&!LZhit){EVlock[k]=lk;EVval[k]=v;}
  return v;
}
function quiesceChk(pos,alpha,beta,ply){
  if(ply>=MAXPLY)return evalX(pos,false,0,0);
  const moves=pos.gen(false);
  for(let i=0;i<moves.length;i++){const m=moves[i];m.score=m.cap?1000+10*VAL[m.cap<0?-m.cap:m.cap]-(m.piece<0?-m.piece:m.piece):0;}
  let legal=0;
  for(let i=0;i<moves.length;i++){
    pickNext(moves,i);
    const m=moves[i];
    pos.make(m);
    if(pos.illegal()){pos.unmake(m);continue;}
    legal++;
    const sc=-quiesce(pos,-beta,-alpha,ply+1);
    pos.unmake(m);
    if(SR.stop)return 0;
    if(sc>=beta)return sc;
    if(sc>alpha)alpha=sc;
  }
  return legal===0?-MATE+ply:alpha;
}

function quiesce(pos,alpha,beta,ply){
  if((++SR.nodes&2047)===0&&SR.deadline&&Date.now()>SR.deadline)SR.stop=true;
  if(SR.stop)return 0;
  if(SR.ex&&pos.inCheck())return quiesceChk(pos,alpha,beta,ply);
  const stand=SR.ex?evalX(pos,true,alpha,beta):(SR.fast?evalX(pos,false,0,0):evaluate(pos));
  if(ply>=MAXPLY)return stand;
  if(stand>=beta)return stand;
  if(stand>alpha)alpha=stand;
  const moves=pos.gen(true);
  for(let i=0;i<moves.length;i++){
    const m=moves[i];
    m.score=m.cap?10*VAL[Math.abs(m.cap)]-Math.abs(m.piece):800;
  }
  const fast=SR.fast;
  if(!fast)moves.sort(byScore);
  for(let i=0;i<moves.length;i++){
    if(fast)pickNext(moves,i);
    const m=moves[i];
    /* 高速探索: どれだけ駒を取っても alpha に届かない取りは読まない(デルタ枝刈り) */
    if(fast&&FO.delta&&!m.promo&&stand+VAL[m.cap<0?-m.cap:m.cap]+200<alpha)continue;
    /* 強化版: ポーンに守られたマスへ、安い駒で取れない損な取りは読まない */
    if(SR.ex&&m.cap&&!m.promo&&VAL[m.cap<0?-m.cap:m.cap]+60<VAL[m.piece<0?-m.piece:m.piece]&&pawnGuards(pos,m.to,m.piece))continue;
    pos.make(m);
    if(pos.illegal()){pos.unmake(m);continue;}
    const sc=-quiesce(pos,-beta,-alpha,ply+1);
    pos.unmake(m);
    if(SR.stop)return 0;
    if(sc>=beta)return sc;
    if(sc>alpha)alpha=sc;
  }
  return alpha;
}

function negamax(pos,depth,alpha,beta,ply){
  if(SR.fast)return negamaxF(pos,depth,alpha,beta,ply);
  if((++SR.nodes&2047)===0&&SR.deadline&&Date.now()>SR.deadline)SR.stop=true;
  if(SR.stop)return 0;
  /* 50手ルールよりメイト成立が優先(FIDE)。pro の A-2/A-9 と同じ扱い */
  if(pos.isRepetition())return 0;
  if(pos.half>=100){
    if(pos.inCheck()&&!pos.hasLegalMove())return -MATE+ply;
    return 0;
  }
  /* 王手延長で深く入りすぎてkiller記録などが壊れないようにする(negamaxFと同じガード) */
  if(ply>=MAXPLY-1)return evaluate(pos);
  const inCheck=pos.inCheck();
  if(inCheck&&SR.ext&&ply<MAXPLY-8)depth++;
  if(depth<=0)return SR.useQ?quiesce(pos,alpha,beta,ply):evaluate(pos);
  const key=pos.h1&TT_MASK;
  let ttEnc=-1;
  if(TTflag[key]!==0&&TTlock[key]===pos.h2){
    ttEnc=TTmove[key];
    if(TTdepth[key]>=depth){
      let sc=TTscore[key];
      if(sc>MATE-1000)sc-=ply;else if(sc<-MATE+1000)sc+=ply;
      const fl=TTflag[key];
      if(fl===1)return sc;
      if(fl===2&&sc>=beta)return sc;
      if(fl===3&&sc<=alpha)return sc;
    }
  }
  if(SR.nmp&&!inCheck&&depth>=3&&ply>0&&SR.noNullAt!==ply&&beta<MATE-1000&&beta>-MATE+1000&&pos.hasPieces(pos.turn)){
    if(evaluate(pos)>=beta){
      const saved=SR.noNullAt;
      SR.noNullAt=ply+1;
      pos.makeNull();
      const nsc=-negamax(pos,depth-3,-beta,-beta+1,ply+1);
      pos.unmakeNull();
      SR.noNullAt=saved;
      if(SR.stop)return 0;
      if(nsc>=beta)return beta;
    }
  }
  const moves=pos.gen(false);
  const kl=SR.killers[ply];
  for(let i=0;i<moves.length;i++)moves[i].score=scoreMove(moves[i],ttEnc,kl);
  moves.sort(byScore);
  const origAlpha=alpha;
  let best=-INF,bestEnc=0,legal=0;
  for(let i=0;i<moves.length;i++){
    const m=moves[i];
    pos.make(m);
    if(pos.illegal()){pos.unmake(m);continue;}
    legal++;
    const quiet=!m.cap&&!m.promo;
    let sc;
    if(SR.lmr&&i>=4&&depth>=3&&quiet&&!inCheck&&!pos.inCheck()){
      sc=-negamax(pos,depth-2,-alpha-1,-alpha,ply+1);
      if(sc>alpha)sc=-negamax(pos,depth-1,-beta,-alpha,ply+1);
    }else{
      sc=-negamax(pos,depth-1,-beta,-alpha,ply+1);
    }
    pos.unmake(m);
    if(SR.stop)return 0;
    if(sc>best){best=sc;bestEnc=m.enc;if(sc>alpha)alpha=sc;}
    if(alpha>=beta){
      if(quiet){
        const k=SR.killers[ply];
        if(k[0]!==m.enc){k[1]=k[0];k[0]=m.enc;}
        SR.history[(m.piece+6)*64+m.to]+=depth*depth;
      }
      break;
    }
  }
  if(legal===0)return inCheck?-MATE+ply:0;
  let st=best;
  if(st>MATE-1000)st+=ply;else if(st<-MATE+1000)st-=ply;
  TTlock[key]=pos.h2;TTscore[key]=st;TTdepth[key]=depth;TTmove[key]=bestEnc;
  TTflag[key]=best>=beta?2:(best>origAlpha?1:3);
  return best;
}

/* ---- 高速探索(レベル???用)。同じ時間でより深く読むための工夫をまとめたもの ----
   FO は各工夫のオン/オフ(検証用)。
   pvs  : 最初の手だけ全幅で読み、残りは「今の最善を超えるか」だけを狭い窓で確かめる
   lmr  : 後ろの方の静かな手を、深さと順位に応じて浅く読む
   rfp  : 評価がベータを大きく超えている浅い局面は、読まずに打ち切る
   nmp  : パスしても有利なら打ち切る。深いほど大きく省略する
   fut  : 浅い局面で、どう指しても alpha に届きそうにない静かな手は読まない
   lmp  : 浅い局面で、順位が低すぎる静かな手は読まない
   iir  : 置換表に手が無い局面は、少し浅く読む
   hist : ベータを超えた静かな手を褒め、その前に試した手は減点する
   bad  : ポーンに守られたマスへの損な取りは後回し
   delta: 静止探索で、取っても届かない取りは読まない
   asp  : 前回の評価の近くに絞った窓で最初から読む */
const FO={pvs:1,lmr:1,rfp:1,nmp:1,fut:1,lmp:1,iir:1,hist:1,bad:1,delta:1,asp:1};
const LMRT=[];
(function(){
  for(let d=0;d<64;d++){
    LMRT[d]=[];
    for(let m=0;m<64;m++)LMRT[d][m]=(d<1||m<1)?0:Math.floor(0.75+Math.log(d)*Math.log(m)/2.25);
  }
})();

function negamaxF(pos,depth,alpha,beta,ply){
  if((++SR.nodes&2047)===0&&SR.deadline&&Date.now()>SR.deadline)SR.stop=true;
  if(SR.stop)return 0;
  /* 50手ルールよりメイト成立が優先(FIDE)。pro の A-2/A-9 と同じ扱い */
  if(pos.isRepetition())return 0;
  if(pos.half>=100){
    if(pos.inCheck()&&!pos.hasLegalMove())return -MATE+ply;
    return 0;
  }
  if(ply>=MAXPLY-1)return evaluate(pos);
  /* 詰みまでの手数より遠い評価は意味がないので窓を狭める */
  if(alpha<-MATE+ply)alpha=-MATE+ply;
  if(beta>MATE-ply-1)beta=MATE-ply-1;
  if(alpha>=beta)return alpha;
  const inCheck=pos.inCheck();
  if(inCheck&&ply<MAXPLY-8)depth++;
  if(depth<=0)return quiesce(pos,alpha,beta,ply);
  const pv=beta-alpha>1;
  const key=pos.h1&TT_MASK;
  let ttEnc=-1;
  if(TTflag[key]!==0&&TTlock[key]===pos.h2){
    ttEnc=TTmove[key];
    if(TTdepth[key]>=depth){
      let sc=TTscore[key];
      if(sc>MATE-1000)sc-=ply;else if(sc<-MATE+1000)sc+=ply;
      const fl=TTflag[key];
      if(fl===1)return sc;
      if(fl===2&&sc>=beta)return sc;
      if(fl===3&&sc<=alpha)return sc;
    }
  }
  const us=pos.turn;
  const noMate=beta<MATE-1000&&alpha>-MATE+1000;
  const ex=SR.ex;
  let se=0,haveSe=false,improving=false;
  if(!inCheck&&(!pv||ex)){se=evalX(pos,false,0,0);haveSe=!pv;}
  if(ex){
    /* 強化版: 2手前(同じ側の番)より評価が上がっているかを覚えておく */
    SR.ev[ply]=inCheck?-32001:se;
    improving=!inCheck&&ply>=2&&SR.ev[ply-2]>-32000&&se>SR.ev[ply-2];
  }
  if(haveSe&&noMate){
    /* 強化版: 浅い局面で評価が alpha をだいぶ下回るなら、静止探索だけで確かめて打ち切る */
    if(ex&&depth<=2&&se+250*depth<=alpha){
      const rz=quiesce(pos,alpha,alpha+1,ply);
      if(SR.stop)return 0;
      if(rz<=alpha)return rz;
    }
    /* 浅い局面で評価がベータを大きく超えているなら、読むまでもない */
    const rm=130*depth-(improving?60:0);
    if(FO.rfp&&depth<=4&&se-rm>=beta&&pos.hasPieces(us))return se-rm;
    /* パスしても(相手に2手続けて指させても)ベータを超えるなら、実際に指せばもっと良いはず */
    if(FO.nmp&&depth>=3&&ply>0&&SR.noNullAt!==ply&&se>=beta&&pos.hasPieces(us)){
      const R=2+(depth>=6?1:0)+(depth>=10?1:0);
      const saved=SR.noNullAt;
      SR.noNullAt=ply+1;
      pos.makeNull();
      const nsc=-negamaxF(pos,depth-1-R,-beta,-beta+1,ply+1);
      pos.unmakeNull();
      SR.noNullAt=saved;
      if(SR.stop)return 0;
      if(nsc>=beta)return nsc>MATE-1000?beta:nsc;
    }
  }
  if(FO.iir&&ttEnc<0&&depth>=6)depth--;
  const moves=pos.gen(false);
  const kl=SR.killers[ply];
  SR.cur=pos;
  for(let i=0;i<moves.length;i++)moves[i].score=scoreMove(moves[i],ttEnc,kl);
  const origAlpha=alpha;
  const futile=FO.fut&&haveSe&&depth<=3&&alpha>-MATE+1000&&se+150*depth+60<=alpha;
  const lmpLimit=(FO.lmp&&haveSe&&depth<=3)?Math.floor((4+depth*depth*2)*(ex&&!improving?0.75:1)):999;
  let tried=null;
  let best=-INF,bestEnc=0,legal=0;
  for(let i=0;i<moves.length;i++){
    pickNext(moves,i);
    const m=moves[i];
    pos.make(m);
    if(pos.illegal()){pos.unmake(m);continue;}
    legal++;
    const quiet=!m.cap&&!m.promo;
    if(quiet&&legal>1&&!inCheck&&best>-MATE+1000&&(futile||legal>lmpLimit)&&!pos.inCheck()){
      pos.unmake(m);continue;
    }
    const nd=depth-1;
    let sc;
    if(legal===1||!FO.pvs){
      sc=-negamaxF(pos,nd,-beta,-alpha,ply+1);
    }else{
      let R=0;
      if(FO.lmr&&nd>=2&&quiet&&legal>=4&&!inCheck&&!pos.inCheck()){
        R=LMRT[depth<63?depth:63][legal<63?legal:63];
        if(pv)R--;
        if(ex){
          if(!improving)R++;
          const hv=SR.history[(m.piece+6)*64+m.to];
          if(hv>2000)R--;else if(hv<0)R++;
        }
        if(R<0)R=0;
        if(R>nd-1)R=nd-1;
      }
      sc=-negamaxF(pos,nd-R,-alpha-1,-alpha,ply+1);
      if(sc>alpha&&R>0)sc=-negamaxF(pos,nd,-alpha-1,-alpha,ply+1);
      if(sc>alpha&&sc<beta)sc=-negamaxF(pos,nd,-beta,-alpha,ply+1);
    }
    pos.unmake(m);
    if(SR.stop)return 0;
    if(sc>best){best=sc;bestEnc=m.enc;if(sc>alpha)alpha=sc;}
    if(alpha>=beta){
      if(quiet){
        const k=SR.killers[ply];
        if(k[0]!==m.enc){k[1]=k[0];k[0]=m.enc;}
        const bonus=depth*depth;
        SR.history[(m.piece+6)*64+m.to]+=bonus;
        if(FO.hist&&tried){for(let t=0;t<tried.length;t++)SR.history[tried[t]]-=bonus;}
      }
      break;
    }
    if(quiet&&FO.hist){if(!tried)tried=[];tried.push((m.piece+6)*64+m.to);}
  }
  if(legal===0)return inCheck?-MATE+ply:0;
  let st=best;
  if(st>MATE-1000)st+=ply;else if(st<-MATE+1000)st-=ply;
  if(!ex||TTflag[key]===0||TTlock[key]===pos.h2||TTage[key]!==SR.gen||depth+3>=TTdepth[key]){
    TTlock[key]=pos.h2;TTscore[key]=st;TTdepth[key]=depth;TTmove[key]=bestEnc;
    TTflag[key]=best>=beta?2:(best>origAlpha?1:3);TTage[key]=SR.gen;
  }
  return best;
}

function gauss(){return (Math.random()+Math.random()+Math.random()-1.5)*2;}

/* 低レベル用: 全候補手を同じ深さで評価し、点数に乱数(ゆらぎ)を足して選ぶ */
function searchNoisy(pos,legal,depth,noise){
  let best=null,bestSc=-Infinity;
  for(let i=0;i<legal.length;i++){
    const m=legal[i];
    pos.make(m);
    let sc;
    /* 50手ルールよりメイト成立が優先(pro A-2 と同じ扱い) */
    if(!pos.hasLegalMove())sc=pos.inCheck()?MATE:0;
    else if(pos.half>=100)sc=(pos.inCheck()&&!pos.hasLegalMove())?MATE:0;
    else if(pos.isRepetition())sc=0;
    else sc=-negamax(pos,depth-1,-INF,INF,1);
    pos.unmake(m);
    if(SR.stop)break;
    sc+=noise*gauss();
    if(sc>bestSc){bestSc=sc;best=m;}
  }
  return best||legal[0];
}

/* 高レベル用: 反復深化 + αβ + 置換表。時間いっぱいまで読む */
function searchDeep(pos,legal,maxDepth){
  for(let i=0;i<legal.length;i++)legal[i].score=scoreMove(legal[i],-1,null);
  legal.sort(byScore);
  let best=legal[0];
  SR.depthDone=0;SR.bestScore=0;
  for(let d=1;d<=maxDepth;d++){
    let alpha=-INF,iterBest=null,iterScore=-INF;
    for(let i=0;i<legal.length;i++){
      const m=legal[i];
      pos.make(m);
      let sc;
      /* 50手ルールよりメイト成立が優先(pro A-2 と同じ扱い) */
      if(pos.half>=100)sc=(pos.inCheck()&&!pos.hasLegalMove())?MATE:0;
      else if(pos.isRepetition())sc=0;
      else sc=-negamax(pos,d-1,-INF,-alpha,1);
      pos.unmake(m);
      if(SR.stop)break;
      if(sc>iterScore){iterScore=sc;iterBest=m;if(sc>alpha)alpha=sc;}
    }
    if(iterBest){
      best=iterBest;
      SR.bestScore=iterScore;
      const idx=legal.indexOf(best);
      legal.splice(idx,1);legal.unshift(best);
    }
    if(SR.stop)break;
    SR.depthDone=d;
    if(iterScore>MATE-100)break;
    if((Date.now()-SR.start)*2.2>SR.budget)break;
  }
  return best;
}

/* 高速探索のルート: 前回の評価の近くに絞った窓(アスピレーション窓)で読み、
   外れたら窓を広げてやり直す。最初の手以外は「最善手を超えるか」だけを確かめる */
function searchDeepFast(pos,legal,maxDepth){
  SR.cur=pos;
  for(let i=0;i<legal.length;i++)legal[i].score=scoreMove(legal[i],-1,null);
  legal.sort(byScore);
  let best=legal[0];
  SR.depthDone=0;SR.bestScore=0;
  let prev=0;
  for(let d=1;d<=maxDepth;d++){
    let lo=-INF,hi=INF,delta=0;
    if(FO.asp&&d>=5&&prev>-1500&&prev<1500){delta=35;lo=prev-delta;hi=prev+delta;}
    let iterBest=null,iterScore=-INF,aborted=false;
    for(;;){
      let alpha=lo,failHigh=false;
      iterBest=null;iterScore=-INF;
      for(let i=0;i<legal.length;i++){
        const m=legal[i];
        pos.make(m);
        let sc;
        /* 50手ルールよりメイト成立が優先(pro A-2 と同じ扱い) */
        if(pos.half>=100)sc=(pos.inCheck()&&!pos.hasLegalMove())?MATE:0;
        else if(pos.isRepetition())sc=0;
        else if(i===0||!FO.pvs)sc=-negamax(pos,d-1,-hi,-alpha,1);
        else{
          sc=-negamax(pos,d-1,-alpha-1,-alpha,1);
          if(sc>alpha&&sc<hi)sc=-negamax(pos,d-1,-hi,-alpha,1);
        }
        pos.unmake(m);
        if(SR.stop){aborted=true;break;}
        if(sc>iterScore){iterScore=sc;iterBest=m;}
        if(sc>alpha)alpha=sc;
        if(sc>=hi){failHigh=true;break;}
      }
      if(aborted)break;
      if(lo>-INF&&iterScore<=lo){
        /* 予想より悪かった: 下側を広げて、最初からやり直す */
        delta*=2;
        lo=delta>400?-INF:lo-delta;
        continue;
      }
      if(failHigh){
        /* 予想より良かった: 上側を広げてやり直す(見つけた手を先頭に) */
        const idx=legal.indexOf(iterBest);
        legal.splice(idx,1);legal.unshift(iterBest);
        delta*=2;
        hi=delta>400?INF:hi+delta;
        continue;
      }
      break;
    }
    if(aborted){
      /* 途中で時間切れ: 窓の内側(または上)で見つかった手だけ採用する */
      if(iterBest&&iterScore>lo){best=iterBest;SR.bestScore=iterScore;}
      break;
    }
    const unst=SR.ex&&d>=6&&(iterBest!==best||iterScore<prev-25);
    best=iterBest;
    SR.bestScore=iterScore;prev=iterScore;
    const idx=legal.indexOf(best);
    legal.splice(idx,1);legal.unshift(best);
    SR.depthDone=d;
    if(iterScore>MATE-100)break;
    if((Date.now()-SR.start)*(unst?1.4:2.0)>SR.budget)break;
  }
  return best;
}

/* レベル表: d=先読み手数, noise=評価のゆらぎ(センチポーン), q=静止探索, ext=王手延長, lmr=後ろの手を浅く読む, t=思考時間の上限(ms) */
const LEVELS=[null,
 {d:1,noise:900,q:0,ext:0,lmr:0,t:4000},
 {d:1,noise:600,q:0,ext:0,lmr:0,t:4000},
 {d:1,noise:380,q:0,ext:0,lmr:0,t:4000},
 {d:1,noise:220,q:0,ext:0,lmr:0,t:4000},
 {d:2,noise:240,q:0,ext:0,lmr:0,t:4000},
 {d:2,noise:150,q:0,ext:0,lmr:0,t:4000},
 {d:2,noise:90,q:1,ext:0,lmr:0,t:4000},
 {d:3,noise:90,q:1,ext:0,lmr:0,t:4000},
 {d:3,noise:60,q:1,ext:0,lmr:0,t:4000},
 {d:3,noise:35,q:1,ext:1,lmr:0,t:4000},
 {d:3,noise:20,q:1,ext:1,lmr:1,t:4000},
 {d:4,noise:20,q:1,ext:1,lmr:1,t:4000},
 {d:4,noise:0,q:1,ext:1,lmr:1,t:600},
 {d:5,noise:0,q:1,ext:1,lmr:1,t:900},
 {d:6,noise:0,q:1,ext:1,lmr:1,t:1200},
 {d:7,noise:0,q:1,ext:1,lmr:1,t:1800},
 {d:8,noise:0,q:1,ext:1,lmr:1,t:2600},
 {d:9,noise:0,q:1,ext:1,lmr:1,t:3600},
 {d:10,noise:0,q:1,ext:1,lmr:1,t:5000},
 {d:14,noise:0,q:1,ext:1,lmr:1,t:6500},
 {d:30,noise:0,q:1,ext:1,lmr:1,nmp:1,trap:1,fast:1,t:10000}
];

/* レベル???の強さ段階(小(標準)・中・高・超高・最大)。思考時間の倍率と置換表の大きさ */
const POWER=[1,2,4,8,16];
const POWER_TT=[20,20,21,22,22];

/* 指す手を決める。手が無ければ null。power は ???(レベル21)のときだけ効く段階(0〜4) */
function chooseMove(pos,level,power,ed){
  const pi=Math.max(0,Math.min(POWER.length-1,power|0));
  const L=LEVELS[Math.max(1,Math.min(21,level|0))];
  ensureTT(L.trap?Math.min(22,POWER_TT[pi]+((ed|0)===1?1:0)):20);LAST.depth=0;LAST.trap=false;
  const legal=pos.legalMoves();
  if(legal.length===0)return null;
  if(legal.length===1)return legal[0];
  SR.nodes=0;SR.stop=false;
  SR.useQ=!!L.q;SR.ext=!!L.ext;SR.lmr=!!L.lmr;SR.nmp=!!L.nmp;SR.fast=!!L.fast;SR.cur=pos;SR.noNullAt=-1;
  SR.killers=[];
  for(let i=0;i<MAXPLY+4;i++)SR.killers.push([0,0]);
  SR.history.fill(0);
  /* 強化版(ed=1): 置換表を次の手にも引き継ぐ */
  SR.ex=!!(L.trap&&(ed|0)===1);
  if(SR.ex){SR.gen=(SR.gen+1)&255;SR.ev=new Int32Array(MAXPLY+8);}
  else TTflag.fill(0);
  let noise=L.noise,depth=L.d,time=L.trap?L.t*POWER[pi]:L.t;
  /* 序盤は毎回同じ展開にならないよう、少しだけゆらぎを入れる */
  if(noise===0&&pos.full<=3&&!L.trap){noise=12;depth=Math.min(depth,4);time=2500;}
  SR.start=Date.now();SR.total=time;SR.budget=SR.ex?time*0.95:time;SR.deadline=SR.start+SR.budget;
  if(noise>0){const nm=searchNoisy(pos,legal,depth,noise);LAST.nodes=SR.nodes;LAST.time=Date.now()-SR.start;LAST.score=0;return nm;}
  let m=L.fast?searchDeepFast(pos,legal,depth):searchDeep(pos,legal,depth);
  LAST.depth=SR.depthDone;
  LAST.nodes=SR.nodes;LAST.time=Date.now()-SR.start;LAST.score=SR.bestScore;
  return m;
}

/* 公開するもの。Index.html は Pos / chooseMove / toSAN / START_FEN / LEVELS / POWER / LAST を使う */
globalThis.ChessEngine={Pos:Pos,chooseMove:chooseMove,toSAN:toSAN,evaluate:evaluate,START_FEN:START_FEN,LEVELS:LEVELS,POWER:POWER,perft:perft,LAST:LAST,EV:EV,FO:FO,CFG:CFG,VERSION:'rookie1.0-quick-lite'};
})();
