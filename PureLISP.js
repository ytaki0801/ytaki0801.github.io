//
// PureLISP.js, with same specification of PureLISP.sh
//
// This code is licensed under CC0.
// https://creativecommons.org/publicdomain/zero/1.0/
//


// Basic functions for conscell operations:
// cons, car, cdr, eq, atom
function cons(x, y) { return Object.freeze([x, y]); }
function car(s) { return s[0]; }
function cdr(s) { return s[1]; }
function eq(s1, s2) {
  if ((s1 == false && s2 == null) || (s1 == null && s2 == false))
    return true;
  else
    return s1 === s2;
}
function atom(s) { return typeof s == 'string' || eq(s, null) || eq(s, true) || eq(s, false); }


// S-expression input: s_read

function s_lex(s) {
  s = s.replace(/(\(|\)|\'|\,)/g, ' $1 ');
  return s.split(/\s+/).filter(x => x != '');
}

function s_syn(s) {
  function quote(x, s) {
    if (s.length != 0 && s.slice(-1)[0] == '\'') {
      s.pop();
      return cons("quote", cons(x, null));
    } else {
      return x
    }
  }
  var t = s.pop();
  if (t == ')') {
    var r = null;
    while (s.slice(-1)[0] != '(') {
      if (s.slice(-1)[0] == '.') {
        s.pop();
        r = cons(s_syn(s), car(r));
      } else {
        r = cons(s_syn(s), r);
      }
    }
    s.pop();
    return quote(r, s);
  } else {
    return quote(t, s);
  }
}

function s_read(s) { return s_syn(s_lex(s)); }


// S-expression output: s_string

function s_strcons(s) {
  var sa_r = s_string(car(s));
  var sd = cdr(s);
  if (eq(sd, null)) {
    return sa_r;
  } else if (atom(sd)) {
    return sa_r + ' . ' + sd;
  } else {
    return sa_r + ' ' + s_strcons(sd);
  }
}

function s_string(s) {
  if      (eq(s, null))  return '()';
  else if (eq(s, true))  return 't';
  else if (eq(s, false)) return 'nil';
  else if (atom(s))
    return s;
  else
    return '(' + s_strcons(s) + ')';
}


// The evaluator: s_eval and utility functions

function caar(x) { return car(car(x)); }
function cadr(x) { return car(cdr(x)); }
function cdar(x) { return cdr(car(x)); }
function cadar(x) { return car(cdr(car(x))); }
function caddr(x) { return car(cdr(cdr(x))); }
function cadddr(x) { return car(cdr(cdr(cdr(x)))); }

function s_null(x) { return eq(x, null); }

function s_append(x, y) {
  if (s_null(x)) return y;
  else return cons(car(x), s_append(cdr(x), y));
}

function s_pair(x, y) {
  if (s_null(x) || s_null(y)) return null;
  else if (!atom(x) && !atom(y))
    return cons(cons(car(x), car(y)), s_pair(cdr(x), cdr(y)));
  else if (atom(x))
    return cons(cons(x, y), null);
  else
    return null;
}

function s_assq(x, y) {
  if (s_null(y)) return null;
  else if (eq(caar(y), x)) return cdar(y);
  else return s_assq(x, cdr(y));
}

function s_length(x) {
  if (s_null(x)) return 0;
  else return 1 + s_length(cdr(x));
}

function s_cond(c, a) {
  if (s_eval(caar(c), a)) return s_eval(cadar(c), a);
  else return s_cond(cdr(c), a);
}

const s_builtins = [ "cons", "car", "cdr", "eq", "atom", "length" ];

function s_lookup(t, a) {
  if      (eq(t, "t"))   return true;
  else if (eq(t, "nil")) return false;
  else if (s_builtins.includes(t)) return t;
  else {
    r = s_assq(t, a);
    if (s_null(r)) return s_assq(t, GENV);
    else return r;
  }
}

function s_eargs(v, a) {
  if (s_null(v)) return null;
  else return cons(s_eval(car(v), a), s_eargs(cdr(v), a));
}

function s_eval(e, a) {
  if (atom(e)) return s_lookup(e, a);
  else if (eq(car(e), "quote")) return cadr(e);
  else if (eq(car(e), "cond"))  return s_cond(cdr(e), a);
  else if (eq(car(e), "lambda") || eq(car(e), "macro")) {
    return cons(car(e), cons(cadr(e), cons(caddr(e), cons(a, null))));
  }
  else if (eq(car(e), "def")) {
    GENV = cons(cons(cadr(e), s_eval(caddr(e), a)), GENV);
    return cadr(e);
  } else {
    r = s_eval(car(e), a);
    if (!atom(r) && eq(car(r), "macro"))
      return s_eval(s_apply(r, cdr(e)), a);
    else
      return s_apply(r, s_eargs(cdr(e), a));
  }
}

function s_apply(f, v) {
  if (atom(f)) {
    if      (eq(f, "cons"))   return cons(car(v), cadr(v));
    else if (eq(f, "car"))    return car(car(v));
    else if (eq(f, "cdr"))    return cdr(car(v));
    else if (eq(f, "eq"))     return eq(car(v), cadr(v));
    else if (eq(f, "atom"))   return atom(car(v));
    else if (eq(f, "length")) return String(s_length(car(v)));
  } else {
    lvars = cadr(f);
    lbody = caddr(f);
    lenvs = cadddr(f);
    if (atom(lvars))
      if (s_null(lvars)) return s_eval(lbody, lenvs);
      else return s_eval(lbody, s_append(cons(cons(lvars, v), null), lenvs));
    else
      return s_eval(lbody, s_pair(lvars, v));
  }
}


// REP (no Loop): s_rep
GENV = s_read("()");
function s_rep(e) { return s_string(s_eval(s_read(e), s_read("()"))); }

