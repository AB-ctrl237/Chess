/* ============================================================
   TEJA KING CHESS — chess.js
   Full chess engine: legal moves, check/checkmate/stalemate,
   castling, en passant, pawn promotion, minimax bot w/ alpha-beta
   ============================================================ */

"use strict";

/* ──────────────────────────────────────────
   CONSTANTS
────────────────────────────────────────── */
const FILES = ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h'];

const PIECE_SYMBOLS = {
  wK: '♔', wQ: '♕', wR: '♖', wB: '♗', wN: '♘', wP: '♙',
  bK: '♚', bQ: '♛', bR: '♜', bB: '♝', bN: '♞', bP: '♟',
};

const PIECE_VALUES = { P: 100, N: 320, B: 330, R: 500, Q: 900, K: 20000 };

/* Positional scoring tables (white's perspective; mirror for black) */
const PAWN_TABLE = [
  [  0,  0,  0,  0,  0,  0,  0,  0],
  [ 50, 50, 50, 50, 50, 50, 50, 50],
  [ 10, 10, 20, 30, 30, 20, 10, 10],
  [  5,  5, 10, 25, 25, 10,  5,  5],
  [  0,  0,  0, 20, 20,  0,  0,  0],
  [  5, -5,-10,  0,  0,-10, -5,  5],
  [  5, 10, 10,-20,-20, 10, 10,  5],
  [  0,  0,  0,  0,  0,  0,  0,  0],
];
const KNIGHT_TABLE = [
  [-50,-40,-30,-30,-30,-30,-40,-50],
  [-40,-20,  0,  0,  0,  0,-20,-40],
  [-30,  0, 10, 15, 15, 10,  0,-30],
  [-30,  5, 15, 20, 20, 15,  5,-30],
  [-30,  0, 15, 20, 20, 15,  0,-30],
  [-30,  5, 10, 15, 15, 10,  5,-30],
  [-40,-20,  0,  5,  5,  0,-20,-40],
  [-50,-40,-30,-30,-30,-30,-40,-50],
];
const BISHOP_TABLE = [
  [-20,-10,-10,-10,-10,-10,-10,-20],
  [-10,  0,  0,  0,  0,  0,  0,-10],
  [-10,  0,  5, 10, 10,  5,  0,-10],
  [-10,  5,  5, 10, 10,  5,  5,-10],
  [-10,  0, 10, 10, 10, 10,  0,-10],
  [-10, 10, 10, 10, 10, 10, 10,-10],
  [-10,  5,  0,  0,  0,  0,  5,-10],
  [-20,-10,-10,-10,-10,-10,-10,-20],
];
const ROOK_TABLE = [
  [  0,  0,  0,  0,  0,  0,  0,  0],
  [  5, 10, 10, 10, 10, 10, 10,  5],
  [ -5,  0,  0,  0,  0,  0,  0, -5],
  [ -5,  0,  0,  0,  0,  0,  0, -5],
  [ -5,  0,  0,  0,  0,  0,  0, -5],
  [ -5,  0,  0,  0,  0,  0,  0, -5],
  [ -5,  0,  0,  0,  0,  0,  0, -5],
  [  0,  0,  0,  5,  5,  0,  0,  0],
];
const QUEEN_TABLE = [
  [-20,-10,-10, -5, -5,-10,-10,-20],
  [-10,  0,  0,  0,  0,  0,  0,-10],
  [-10,  0,  5,  5,  5,  5,  0,-10],
  [ -5,  0,  5,  5,  5,  5,  0, -5],
  [  0,  0,  5,  5,  5,  5,  0, -5],
  [-10,  5,  5,  5,  5,  5,  0,-10],
  [-10,  0,  5,  0,  0,  0,  0,-10],
  [-20,-10,-10, -5, -5,-10,-10,-20],
];
const KING_TABLE = [
  [-30,-40,-40,-50,-50,-40,-40,-30],
  [-30,-40,-40,-50,-50,-40,-40,-30],
  [-30,-40,-40,-50,-50,-40,-40,-30],
  [-30,-40,-40,-50,-50,-40,-40,-30],
  [-20,-30,-30,-40,-40,-30,-30,-20],
  [-10,-20,-20,-20,-20,-20,-20,-10],
  [ 20, 20,  0,  0,  0,  0, 20, 20],
  [ 20, 30, 10,  0,  0, 10, 30, 20],
];

function getPosScore(type, col, r, c) {
  const row = col === 'w' ? r : 7 - r;
  const tbl =
    type === 'P' ? PAWN_TABLE   :
    type === 'N' ? KNIGHT_TABLE :
    type === 'B' ? BISHOP_TABLE :
    type === 'R' ? ROOK_TABLE   :
    type === 'Q' ? QUEEN_TABLE  :
    type === 'K' ? KING_TABLE   : null;
  return tbl ? (tbl[row][c] || 0) : 0;
}

/* ──────────────────────────────────────────
   GAME STATE
────────────────────────────────────────── */
let board;       // 8×8 array of piece strings like 'wK', 'bP', or null
let turn;        // 'w' or 'b'
let sel;         // selected square [r,c] or null
let legals;      // legal moves for selected piece
let hist;        // move history array for undo / log
let flipped;     // board orientation
let gameOver;
let ep;          // en-passant target square [r,c] or null
let cast;        // castling rights object
let lastMove;    // {from:[r,c], to:[r,c]}
let mode;        // '2p' | 'bot'
let diff;        // 'easy' | 'medium' | 'hard'
let playerColor; // 'w' | 'b'  (which side the human plays in bot mode)
let botThinking; // debounce flag

/* ──────────────────────────────────────────
   MODE / DIFFICULTY / COLOR CONTROLS
────────────────────────────────────────── */
function setMode(m) {
  mode = m;
  document.getElementById('btn2p').classList.toggle('mode-btn--active', m === '2p');
  document.getElementById('btn2p').classList.toggle('active',           m === '2p');
  document.getElementById('btnBot').classList.toggle('mode-btn--active', m === 'bot');
  document.getElementById('btnBot').classList.toggle('active',           m === 'bot');

  const botOpts = document.getElementById('botOpts');
  botOpts.style.display = m === 'bot' ? 'flex' : 'none';
  botOpts.classList.toggle('hidden', m !== 'bot');

  newGame();
}

function setDiff(d) {
  diff = d;
  ['easy', 'medium', 'hard'].forEach(x => {
    const id = 'd' + x.charAt(0).toUpperCase() + x.slice(1);
    const el = document.getElementById(id);
    el.classList.toggle('diff-btn--active', x === d);
    el.classList.toggle('active',           x === d);
  });
}

function setPlayerColor(c) {
  playerColor = c;
  document.getElementById('cW').classList.toggle('color-btn--active', c === 'w');
  document.getElementById('cW').classList.toggle('active',            c === 'w');
  document.getElementById('cB').classList.toggle('color-btn--active', c === 'b');
  document.getElementById('cB').classList.toggle('active',            c === 'b');
  newGame();
}

/* ──────────────────────────────────────────
   BOARD INITIALISATION
────────────────────────────────────────── */
function initBoard() {
  board = Array(8).fill(null).map(() => Array(8).fill(null));
  const backRank = ['R', 'N', 'B', 'Q', 'K', 'B', 'N', 'R'];
  for (let c = 0; c < 8; c++) {
    board[0][c] = 'b' + backRank[c];
    board[1][c] = 'bP';
    board[6][c] = 'wP';
    board[7][c] = 'w' + backRank[c];
  }
}

function newGame() {
  initBoard();
  turn        = 'w';
  sel         = null;
  legals      = [];
  hist        = [];
  gameOver    = false;
  ep          = null;
  cast        = { wK: true, wR0: true, wR7: true, bK: true, bR0: true, bR7: true };
  lastMove    = null;
  botThinking = false;

  document.getElementById('wCap').innerHTML      = '';
  document.getElementById('bCap').innerHTML      = '';
  document.getElementById('mLog').innerHTML      = '';
  document.getElementById('promoArea').innerHTML = '';
  document.getElementById('thinkingBar').textContent = '';

  renderBoard();
  updateStatus();

  if (mode === 'bot' && turn !== playerColor) {
    setTimeout(doBotMove, 600);
  }
}

/* ──────────────────────────────────────────
   HELPERS
────────────────────────────────────────── */
function toggleFlip() { flipped = !flipped; renderBoard(); }

function inBounds(r, c) { return r >= 0 && r < 8 && c >= 0 && c < 8; }
function pieceColor(p)  { return p ? p[0] : null; }
function pieceType(p)   { return p ? p[1] : null; }

/* ──────────────────────────────────────────
   RENDER
────────────────────────────────────────── */
function renderBoard() {
  const div = document.getElementById('boardDiv');
  div.innerHTML = '';

  const fc = document.getElementById('fCoords');
  fc.innerHTML = '';
  const rc = document.getElementById('rCoords');
  rc.innerHTML = '';

  const files = flipped ? [...FILES].reverse() : FILES;
  const ranks = flipped ? [1,2,3,4,5,6,7,8] : [8,7,6,5,4,3,2,1];

  files.forEach(f => {
    const d = document.createElement('div');
    d.className = 'cf';
    d.textContent = f;
    fc.appendChild(d);
  });

  ranks.forEach(r => {
    const d = document.createElement('div');
    d.className = 'cr';
    d.textContent = r;
    rc.appendChild(d);
  });

  for (let ri = 0; ri < 8; ri++) {
    for (let ci = 0; ci < 8; ci++) {
      const r = flipped ? 7 - ri : ri;
      const c = flipped ? 7 - ci : ci;

      const cell = document.createElement('div');
      cell.className = 'sq ' + ((r + c) % 2 === 0 ? 'light' : 'dark');

      /* Highlights */
      if (sel && sel[0] === r && sel[1] === c) cell.classList.add('selected');
      if (lastMove) {
        if (lastMove.from[0] === r && lastMove.from[1] === c) cell.classList.add('lf');
        if (lastMove.to[0]   === r && lastMove.to[1]   === c) cell.classList.add('lt');
      }
      if (isKingInCheck(turn) &&
          board[r][c] &&
          pieceColor(board[r][c]) === turn &&
          pieceType(board[r][c]) === 'K') {
        cell.classList.add('incheck');
      }

      /* Move indicators */
      const mv = legals.find(m => m.to[0] === r && m.to[1] === c);
      if (mv) {
        const isCapture = (board[r][c] && pieceColor(board[r][c]) !== turn) || mv.ep;
        const indicator = document.createElement('div');
        indicator.className = isCapture ? 'cring' : 'mdot';
        cell.appendChild(indicator);
      }

      /* Piece */
      const piece = board[r][c];
      if (piece) {
        const sp = document.createElement('span');
        sp.className = 'piece ' + (pieceColor(piece) === 'w' ? 'wp' : 'bp');
        sp.textContent = PIECE_SYMBOLS[piece];

        if (pieceType(piece) === 'K') {
          sp.classList.add('kp');
          const badge = document.createElement('span');
          badge.className = 'kb';
          badge.textContent = '👑';
          sp.appendChild(badge);
        }
        cell.appendChild(sp);
      }

      cell.addEventListener('click', () => handleClick(r, c));
      div.appendChild(cell);
    }
  }
}

/* ──────────────────────────────────────────
   CLICK HANDLER
────────────────────────────────────────── */
function handleClick(r, c) {
  if (gameOver || botThinking) return;
  if (mode === 'bot' && turn !== playerColor) return;

  const piece = board[r][c];

  if (sel) {
    const mv = legals.find(m => m.to[0] === r && m.to[1] === c);
    if (mv) { executeMove(mv); return; }
    if (piece && pieceColor(piece) === turn) {
      sel    = [r, c];
      legals = getLegalMoves(r, c);
      renderBoard();
      return;
    }
    sel = null; legals = []; renderBoard();
    return;
  }

  if (piece && pieceColor(piece) === turn) {
    sel    = [r, c];
    legals = getLegalMoves(r, c);
    renderBoard();
  }
}

/* ──────────────────────────────────────────
   MOVE GENERATION
────────────────────────────────────────── */
function getLegalMoves(r, c) {
  return getPseudoMoves(r, c).filter(m => {
    const savedBoard = JSON.parse(JSON.stringify(board));
    const savedEP    = ep;
    applyMoveToBoard(board, m);
    const inCheck = isKingInCheck(turn);
    for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) board[i][j] = savedBoard[i][j];
    ep = savedEP;
    return !inCheck;
  });
}

/**
 * Returns pseudo-legal moves (may leave own king in check).
 * @param {boolean} forAttack  When true, pawn attack squares are returned
 *                             instead of push squares (used for isAttacked()).
 */
function getPseudoMoves(r, c, forAttack = false) {
  const p = board[r][c];
  if (!p) return [];
  const col  = pieceColor(p);
  const type = pieceType(p);
  const moves = [];

  const add = (tr, tc, opts = {}) => {
    if (inBounds(tr, tc)) moves.push({ from: [r, c], to: [tr, tc], ...opts });
  };

  /* ----- Pawn ----- */
  if (type === 'P') {
    const dir   = col === 'w' ? -1 : 1;
    const start = col === 'w' ? 6  : 1;

    if (!forAttack) {
      if (inBounds(r + dir, c) && !board[r + dir][c]) {
        add(r + dir, c);
        if (r === start && !board[r + 2 * dir][c]) add(r + 2 * dir, c, { doublePush: true });
      }
    }

    [-1, 1].forEach(dc => {
      if (!inBounds(r + dir, c + dc)) return;
      if (forAttack) {
        add(r + dir, c + dc);
      } else {
        if (board[r + dir][c + dc] && pieceColor(board[r + dir][c + dc]) !== col)
          add(r + dir, c + dc);
        if (ep && ep[0] === r + dir && ep[1] === c + dc)
          add(r + dir, c + dc, { ep: true, epCap: [r, c + dc] });
      }
    });
  }

  /* ----- Knight ----- */
  else if (type === 'N') {
    [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]].forEach(([dr, dc]) => {
      const tr = r + dr, tc = c + dc;
      if (inBounds(tr, tc) && (forAttack || pieceColor(board[tr][tc]) !== col)) add(tr, tc);
    });
  }

  /* ----- King ----- */
  else if (type === 'K') {
    for (let dr = -1; dr <= 1; dr++) {
      for (let dc = -1; dc <= 1; dc++) {
        if (!dr && !dc) continue;
        const tr = r + dr, tc = c + dc;
        if (inBounds(tr, tc) && (forAttack || pieceColor(board[tr][tc]) !== col)) add(tr, tc);
      }
    }

    /* Castling (never for attack scans) */
    if (!forAttack && cast[col + 'K']) {
      /* Kingside */
      if (cast[col + 'R7'] &&
          !board[r][5] && !board[r][6] &&
          !isSquareAttacked(r, 4, col) &&
          !isSquareAttacked(r, 5, col) &&
          !isSquareAttacked(r, 6, col)) {
        add(r, 6, { castle: 'ks' });
      }
      /* Queenside */
      if (cast[col + 'R0'] &&
          !board[r][3] && !board[r][2] && !board[r][1] &&
          !isSquareAttacked(r, 4, col) &&
          !isSquareAttacked(r, 3, col) &&
          !isSquareAttacked(r, 2, col)) {
        add(r, 2, { castle: 'qs' });
      }
    }
  }

  /* ----- Sliding pieces (R / B / Q) ----- */
  else {
    const dirs =
      type === 'R' ? [[0,1],[0,-1],[1,0],[-1,0]] :
      type === 'B' ? [[1,1],[1,-1],[-1,1],[-1,-1]] :
      /* Q */        [[0,1],[0,-1],[1,0],[-1,0],[1,1],[1,-1],[-1,1],[-1,-1]];

    dirs.forEach(([dr, dc]) => {
      let tr = r + dr, tc = c + dc;
      while (inBounds(tr, tc)) {
        if (board[tr][tc]) {
          if (forAttack || pieceColor(board[tr][tc]) !== col) add(tr, tc);
          break;
        }
        add(tr, tc);
        tr += dr; tc += dc;
      }
    });
  }

  return moves;
}

/* ──────────────────────────────────────────
   ATTACK / CHECK DETECTION
────────────────────────────────────────── */
function isSquareAttacked(r, c, byOpponentOf) {
  const opponent = byOpponentOf === 'w' ? 'b' : 'w';
  for (let i = 0; i < 8; i++) {
    for (let j = 0; j < 8; j++) {
      if (board[i][j] && pieceColor(board[i][j]) === opponent) {
        if (getPseudoMoves(i, j, true).some(m => m.to[0] === r && m.to[1] === c)) return true;
      }
    }
  }
  return false;
}

function isKingInCheck(col) {
  for (let i = 0; i < 8; i++) {
    for (let j = 0; j < 8; j++) {
      if (board[i][j] === col + 'K') return isSquareAttacked(i, j, col);
    }
  }
  return false; // King not found (shouldn't happen in normal play)
}

/* ──────────────────────────────────────────
   APPLY MOVE (mutates supplied board)
────────────────────────────────────────── */
function applyMoveToBoard(b, m) {
  const [fr, fc] = m.from;
  const [tr, tc] = m.to;
  const piece = b[fr][fc];

  b[tr][tc] = piece;
  b[fr][fc] = null;

  /* En passant capture */
  if (m.ep && m.epCap) b[m.epCap[0]][m.epCap[1]] = null;

  /* Castling: move the rook */
  if (m.castle === 'ks') { b[fr][5] = b[fr][7]; b[fr][7] = null; }
  if (m.castle === 'qs') { b[fr][3] = b[fr][0]; b[fr][0] = null; }

  /* Update en-passant target */
  ep = m.doublePush ? [fr + (tr > fr ? 1 : -1), tc] : null;
}

/* ──────────────────────────────────────────
   EXECUTE MOVE (human or bot)
────────────────────────────────────────── */
function executeMove(mv, isBotMove = false) {
  const [fr, fc] = mv.from;
  const [tr, tc] = mv.to;
  const piece = board[fr][fc];
  const col   = pieceColor(piece);
  const captured = mv.ep ? board[mv.epCap[0]][mv.epCap[1]] : board[tr][tc];
  const notation = buildNotation(mv, piece, captured);

  applyMoveToBoard(board, mv);

  /* Update castling rights */
  if (pieceType(piece) === 'K')  cast[col + 'K']  = false;
  if (pieceType(piece) === 'R') {
    if (fc === 0) cast[col + 'R0'] = false;
    if (fc === 7) cast[col + 'R7'] = false;
  }

  /* Show capture */
  if (captured) {
    const capDiv = document.getElementById(col === 'w' ? 'wCap' : 'bCap');
    capDiv.innerHTML += `<span>${PIECE_SYMBOLS[captured]}</span>`;
  }

  lastMove = { from: [fr, fc], to: [tr, tc] };

  /* Pawn promotion */
  const isPromo = pieceType(piece) === 'P' && (tr === 0 || tr === 7);
  if (isPromo && !isBotMove) {
    sel = null; legals = [];
    renderBoard();
    showPromotionModal(tr, tc, col, notation);
    return;
  }
  if (isPromo && isBotMove) board[tr][tc] = col + 'Q';

  finishMove(notation);
}

/* ──────────────────────────────────────────
   PAWN PROMOTION MODAL
────────────────────────────────────────── */
function showPromotionModal(r, c, col, notation) {
  const area = document.getElementById('promoArea');
  area.innerHTML = `
    <div class="promo-wrap">
      <div class="promo-inner">
        <h3>👑 PROMOTE YOUR PAWN</h3>
        <div class="pchoices" id="pc"></div>
      </div>
    </div>`;

  ['Q', 'R', 'B', 'N'].forEach(t => {
    const btn = document.createElement('button');
    btn.className   = 'pbtn';
    btn.textContent = PIECE_SYMBOLS[col + t];
    btn.onclick = () => {
      board[r][c] = col + t;
      area.innerHTML = '';
      finishMove(notation + '=' + t);
    };
    document.getElementById('pc').appendChild(btn);
  });
}

/* ──────────────────────────────────────────
   FINISH MOVE — switch turn, check game state
────────────────────────────────────────── */
function finishMove(notation) {
  const movingCol = turn;
  turn = turn === 'w' ? 'b' : 'w';
  sel  = null;
  legals = [];

  const inCheck  = isKingInCheck(turn);
  const allMoves = getAllLegalMoves(turn);

  if (allMoves.length === 0) {
    if (inCheck) notation += '#';
    gameOver = true;
  } else if (inCheck) {
    notation += '+';
  }

  appendMoveToLog(notation, movingCol);
  hist.push({
    board:     JSON.parse(JSON.stringify(board)),
    turn,
    ep,
    cast:      JSON.parse(JSON.stringify(cast)),
    lastMove,
    notation,
  });

  renderBoard();
  updateStatus(inCheck, allMoves.length === 0);

  /* Trigger bot if applicable */
  if (!gameOver && mode === 'bot' && turn !== playerColor) {
    botThinking = true;
    document.getElementById('thinkingBar').textContent = '🤖 Bot is thinking...';
    const delay = diff === 'easy' ? 250 : diff === 'medium' ? 500 : 900;
    setTimeout(doBotMove, delay);
  }
}

/* ──────────────────────────────────────────
   ALL LEGAL MOVES FOR A COLOUR
────────────────────────────────────────── */
function getAllLegalMoves(col) {
  const moves = [];
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      if (board[r][c] && pieceColor(board[r][c]) === col) {
        moves.push(...getLegalMoves(r, c));
      }
    }
  }
  return moves;
}

/* ──────────────────────────────────────────
   ALGEBRAIC NOTATION
────────────────────────────────────────── */
function buildNotation(mv, piece, captured) {
  const [fr, fc] = mv.from;
  const [tr, tc] = mv.to;
  const type = pieceType(piece);

  if (mv.castle === 'ks') return 'O-O';
  if (mv.castle === 'qs') return 'O-O-O';

  let n = type === 'P' ? '' : type;
  if (type === 'P' && (captured || mv.ep)) n = FILES[fc];
  if (captured || mv.ep) n += 'x';
  n += FILES[tc] + (8 - tr);
  return n;
}

/* ──────────────────────────────────────────
   MOVE LOG
────────────────────────────────────────── */
function appendMoveToLog(notation, col) {
  const log = document.getElementById('mLog');
  const moveNum = Math.ceil(hist.length / 2) + 1;

  if (col === 'w') {
    const row = document.createElement('div');
    row.className = 'mrow';
    row.innerHTML = `
      <span class="mnum">${moveNum}.</span>
      <span id="wm${moveNum}">${notation}</span>
      <span id="bm${moveNum}" style="color:#aaa;opacity:0.6;margin-left:4px"></span>`;
    log.appendChild(row);
  } else {
    const bSpan = document.getElementById('bm' + (moveNum - 1));
    if (bSpan) bSpan.textContent = notation;
  }
  log.scrollTop = log.scrollHeight;
}

/* ──────────────────────────────────────────
   STATUS BAR
────────────────────────────────────────── */
function updateStatus(inCheck = false, noMoves = false) {
  const td = document.getElementById('turnDisp');
  const sm = document.getElementById('statMsg');
  const botCol = mode === 'bot' ? (playerColor === 'w' ? 'b' : 'w') : null;

  /* Clear thinking indicator */
  document.getElementById('thinkingBar').textContent = '';
  botThinking = false;

  /* Remove all colour classes */
  td.classList.remove('status-turn--white', 'status-turn--black', 'status-turn--gold');

  if (gameOver) {
    td.classList.add('status-turn--gold');
    if (inCheck && noMoves) {
      const winner = turn === 'w' ? 'BLACK' : 'WHITE';
      td.textContent = `♛ ${winner} WINS! ♛`;
      sm.textContent = 'Checkmate — start a new game';
    } else {
      td.textContent = '⚖ STALEMATE — DRAW';
      sm.textContent = 'No legal moves available';
    }
    return;
  }

  const isBot = mode === 'bot' && turn === botCol;
  td.classList.add(turn === 'w' ? 'status-turn--white' : 'status-turn--black');

  if (inCheck) {
    td.textContent = turn === 'w' ? '⚪ WHITE — CHECK! ⚠' : '⚫ BLACK — CHECK! ⚠';
    sm.textContent = '👑 King is under attack — defend!';
  } else {
    let label;
    if (mode === 'bot') {
      label = isBot
        ? '🤖 BOT IS THINKING...'
        : (turn === 'w' ? '⚪ YOUR TURN (WHITE)' : '⚫ YOUR TURN (BLACK)');
    } else {
      label = turn === 'w' ? "⚪ WHITE'S TURN" : "⚫ BLACK'S TURN";
    }
    td.textContent = label;
    sm.textContent = isBot ? 'Calculating best move...' : 'Choose your next move wisely';
  }
}

/* ──────────────────────────────────────────
   UNDO
────────────────────────────────────────── */
function undoMove() {
  if (!hist.length) return;

  /* In bot mode, undo two half-moves so the human gets their turn back */
  if (mode === 'bot' && hist.length >= 2) { hist.pop(); hist.pop(); }
  else hist.pop();

  if (hist.length) {
    const prev = hist[hist.length - 1];
    board    = JSON.parse(JSON.stringify(prev.board));
    turn     = prev.turn;
    ep       = prev.ep;
    cast     = JSON.parse(JSON.stringify(prev.cast));
    lastMove = prev.lastMove;
  } else {
    initBoard();
    turn     = 'w';
    ep       = null;
    cast     = { wK: true, wR0: true, wR7: true, bK: true, bR0: true, bR7: true };
    lastMove = null;
  }

  sel = null; legals = []; gameOver = false; botThinking = false;
  rebuildMoveLog();
  renderBoard();
  updateStatus(isKingInCheck(turn), false);
}

function rebuildMoveLog() {
  const log = document.getElementById('mLog');
  log.innerHTML = '';
  hist.forEach((h, i) => {
    const col = i % 2 === 0 ? 'w' : 'b';
    const mn  = Math.floor(i / 2) + 1;
    if (col === 'w') {
      const row = document.createElement('div');
      row.className = 'mrow';
      row.innerHTML = `
        <span class="mnum">${mn}.</span>
        <span id="wm${mn}">${h.notation}</span>
        <span id="bm${mn}" style="color:#aaa;opacity:0.6;margin-left:4px"></span>`;
      log.appendChild(row);
    } else {
      const b = document.getElementById('bm' + mn);
      if (b) b.textContent = h.notation;
    }
  });
  log.scrollTop = log.scrollHeight;
}

/* ──────────────────────────────────────────
   BOT — MOVE SELECTION
────────────────────────────────────────── */
function doBotMove() {
  const botCol = playerColor === 'w' ? 'b' : 'w';
  const moves  = getAllLegalMoves(botCol);
  if (!moves.length) return;

  let chosen;
  if (diff === 'easy')        chosen = moves[Math.floor(Math.random() * moves.length)];
  else if (diff === 'medium') chosen = pickBestMove(botCol, 1);
  else                        chosen = pickBestMove(botCol, 2);

  document.getElementById('thinkingBar').textContent = '';
  botThinking = false;
  if (chosen) executeMove(chosen, true);
}

/* ──────────────────────────────────────────
   BOT — BOARD EVALUATION
────────────────────────────────────────── */
function evaluateBoard() {
  let score = 0;
  for (let r = 0; r < 8; r++) {
    for (let c = 0; c < 8; c++) {
      const p = board[r][c];
      if (!p) continue;
      const type   = pieceType(p);
      const col    = pieceColor(p);
      const base   = PIECE_VALUES[type] || 0;
      const pos    = getPosScore(type, col, r, c);
      score += (col === 'w' ? 1 : -1) * (base + pos);
    }
  }
  return score;
}

/* ──────────────────────────────────────────
   BOT — MINIMAX WITH ALPHA-BETA PRUNING
────────────────────────────────────────── */
function minimax(depth, alpha, beta, maximising) {
  if (depth === 0) return evaluateBoard();

  const col   = maximising ? 'b' : 'w';
  const moves = getAllLegalMoves(col);
  if (!moves.length) return maximising ? -99999 : 99999;

  if (maximising) {
    let best = -Infinity;
    for (const mv of moves) {
      const sb = JSON.parse(JSON.stringify(board));
      const se = ep;
      const sc = JSON.parse(JSON.stringify(cast));

      applyMoveToBoard(board, mv);
      /* Auto-promote to queen for the bot */
      if (pieceType(board[mv.to[0]][mv.to[1]]) === 'P' &&
          (mv.to[0] === 0 || mv.to[0] === 7)) board[mv.to[0]][mv.to[1]] = 'bQ';

      const val = minimax(depth - 1, alpha, beta, false);

      for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) board[i][j] = sb[i][j];
      ep = se;
      for (const k in sc) cast[k] = sc[k];

      best  = Math.max(best, val);
      alpha = Math.max(alpha, val);
      if (beta <= alpha) break; /* Prune */
    }
    return best;

  } else {
    let best = Infinity;
    for (const mv of moves) {
      const sb = JSON.parse(JSON.stringify(board));
      const se = ep;
      const sc = JSON.parse(JSON.stringify(cast));

      applyMoveToBoard(board, mv);
      if (pieceType(board[mv.to[0]][mv.to[1]]) === 'P' &&
          (mv.to[0] === 0 || mv.to[0] === 7)) board[mv.to[0]][mv.to[1]] = 'wQ';

      const val = minimax(depth - 1, alpha, beta, true);

      for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) board[i][j] = sb[i][j];
      ep = se;
      for (const k in sc) cast[k] = sc[k];

      best = Math.min(best, val);
      beta = Math.min(beta, val);
      if (beta <= alpha) break; /* Prune */
    }
    return best;
  }
}

function pickBestMove(col, depth) {
  const moves = getAllLegalMoves(col);
  if (!moves.length) return null;

  let bestVal = col === 'b' ? -Infinity : Infinity;
  let best    = moves[0];

  for (const mv of moves) {
    const sb = JSON.parse(JSON.stringify(board));
    const se = ep;
    const sc = JSON.parse(JSON.stringify(cast));

    applyMoveToBoard(board, mv);
    if (pieceType(board[mv.to[0]][mv.to[1]]) === 'P' &&
        (mv.to[0] === 0 || mv.to[0] === 7)) board[mv.to[0]][mv.to[1]] = col + 'Q';

    const val = minimax(
      depth,
      col === 'b' ? -Infinity : Infinity,
      col === 'b' ?  Infinity : -Infinity,
      col !== 'b',
    );

    for (let i = 0; i < 8; i++) for (let j = 0; j < 8; j++) board[i][j] = sb[i][j];
    ep = se;
    for (const k in sc) cast[k] = sc[k];

    if (col === 'b' ? val > bestVal : val < bestVal) {
      bestVal = val;
      best    = mv;
    }
  }
  return best;
}

/* ──────────────────────────────────────────
   BOOT
────────────────────────────────────────── */
mode        = '2p';
diff        = 'easy';
playerColor = 'w';
flipped     = false;

newGame();