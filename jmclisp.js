//
// JMC Lisp: defined in McCarthy's 1960 paper,
// with S-expression input/output and basic list processing
//


// basic list processing: cons, car, cdr, eq, atom
function cons(x, y) { return Object.freeze([x, y]); }
function car(s) { return s[0]; }
function cdr(s) { return s[1]; }
function eq(s1, s2) { return s1 === s2; }
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


// JMC Lisp evaluator: s_eval

function caar(x) { return car(car(x)); }
function cadr(x) { return car(cdr(x)); }
function cadar(x) { return car(cdr(car(x))); }
function caddr(x) { return car(cdr(cdr(x))); }
function caddar(x) { return car(cdr(cdr(car(x)))); }

function s_null(x) { return eq(x, null); }

function s_append(x, y) {
  if (s_null(x)) return y;
  else return cons(car(x), s_append(cdr(x), y));
}

function s_list(x, y) { return cons(x, cons(y, null)); }

function s_pair(x, y) {
  if (s_null(x) && s_null(y)) return null;
  else if (!atom(x) && !atom(y))
    return cons(s_list(car(x), car(y)), s_pair(cdr(x), cdr(y)));
}

function s_assoc(x, y) {
  if (eq(caar(y), x)) return cadar(y);
  else return s_assoc(x, cdr(y));
}

function s_eval(e, a) {
  if      (eq(e, "t"))   return true;
  else if (eq(e, "nil")) return false
  else if (atom(e)) return s_assoc(e, a);
  else if (atom(car(e))) {
    if      (eq(car(e), "quote")) return cadr(e);
    else if (eq(car(e), "atom"))  return atom(s_eval(cadr(e), a));
    else if (eq(car(e), "eq"))    return eq(  s_eval(cadr(e), a),
                                              s_eval(caddr(e), a));
    else if (eq(car(e), "car"))   return car( s_eval(cadr(e), a));
    else if (eq(car(e), "cdr"))   return cdr( s_eval(cadr(e), a));
    else if (eq(car(e), "cons"))  return cons(s_eval(cadr(e), a),
                                             s_eval(caddr(e), a));
    else if (eq(car(e), "cond"))  return evcon(cdr(e), a);
    else return s_eval(cons(s_assoc(car(e), a), cdr(e)), a);
  } else if (eq(caar(e), "lambda"))
      return s_eval(caddar(e),
                    s_append(s_pair(cadar(e), evlis(cdr(e), a)), a));
  else console.log("Error");
}

function evcon(c, a) {
  if (s_eval(caar(c), a)) return s_eval(cadar(c), a);
  else return evcon(cdr(c), a);
}

function evlis(m, a) {
  if (s_null(m)) return null;
  else return cons(s_eval(car(m), a), evlis(cdr(m), a));
}


// REP (no Loop): s_rep
function s_rep(e) { return s_string(s_eval(s_read(e), s_read("()"))); }

