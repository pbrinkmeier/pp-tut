/*
board([
    [s, o, n, w],
    [a, h, e, j],
    [k, n, a, i],
    [t, o, d, w]
]).
*/

board([
	[B11, B21, B31, B41],
    [B12, B22, B32, B42],
    [B13, B23, B33, B43],
    [B14, B24, B34, B44]
]) :-
    Dice = [
        [a, e, a, n, e, g],
        [w, n, g, e, e, h],
        [a, h, s, p, c, o],
        [l, n, h, n, r, z],
        [a, s, p, f, f, k],
        [t, s, t, i, y, d],
        [o, b, j, o, a, b],
        [o, w, t, o, a, t],
        [i, o, t, m, u, c],
        [e, r, t, t, y, l],
        [r, y, v, d, e, l],
        [t, o, e, s, s, i],
        [l, r, e, i, x, d],
        [t, e, r, w, h, v],
        [e, i, u, n, e, s],
        [n, u, i, h, m, q]
    ],
    random_permutation(Dice, DiceShuf),
    DiceShuf = [D1, D2, D3, D4, D5, D6, D7, D8, D9, D10, D11, D12, D13, D14, D15, D16],
    random_member(B11, D1),
    random_member(B21, D2),
    random_member(B31, D3),
    random_member(B41, D4),
    random_member(B12, D5),
    random_member(B22, D6),
    random_member(B32, D7),
    random_member(B42, D8),
    random_member(B13, D9),
    random_member(B23, D10),
    random_member(B33, D11),
    random_member(B43, D12),
    random_member(B14, D13),
    random_member(B24, D14),
    random_member(B34, D15),
    random_member(B44, D16).

% Unfiziert C mit Wert in Zeile Y, Spalte X
% Nützlich: nth1(Index, Liste, Eintrag)
% Beispiel:
% ?- matchCharAt(X, Y, n).
% X = 3, Y = 1 ;
% X = 2, Y = 3.
matchCharAt(X, Y, C) :-
    board(B),
    ...

% Belegt (X1, Y1) mit den direkten und diagonalen Nachbarn von (X, Y).
% Beispiel:
% ?- neighbor((3, 3), (X1, Y1)).
% X1 = 2, Y1 = 2 ;
% X1 = 2, Y1 = 3 ;
% X1 = 2, Y1 = 4 ;
% X1 = 3, Y1 = 2 ;
% X1 = 3, Y1 = 4 ;
% X1 = 4, Y1 = 2 ;
% X1 = 4, Y1 = 3 ;
% X1 = 4, Y1 = 4.
neighbor((X, Y), (X1, Y1)) :-
    ...

% Finde alle *unterschiedlichen* Listen von Positionen, an denen Word vorkommt.
% Beispiel:
% ?- solve([s, o, h, n], P).
% P = [(1,1), (2,1), (2,2), (2,3)] ;
% P = [(1,1), (2,1), (2,2), (3,1)].
% Hier bitte nichts ändern sondern nur search unten ausfüllen.
solve(Word, Positions) :-
    member(X, [1, 2, 3, 4]),
    member(Y, [1, 2, 3, 4]),
    search(Word, (X, Y), [], Positions).

% search(Word, Pos, Visited, Positions)
% Finde Liste Positions ausgehend von und inklusive Pos sodass
% Positions einen Pfad auf dem Spielbrett beschreibt der Word bildet.
% Soll für keine Lösung für Word = [] haben!
% Verwendet matchCharAt und neighbor. Vermeidet Schleifen indem ihr
% besuchte Positionen in Visited speichert. 
search([C], (X, Y), _, [(X, Y)]) :-
    ...
search([C|Cs], (X, Y), Visited, [(X, Y) | Positions]) :-
    ...

% Schamlos kopiert
% von http://www.scrabble3d.info/t286f21-Liste-fast-aller-Woerter-mit-drei-Buchstaben.html
% und http://www.sobiki.de/4buchstaben.html
% Welche Abfrage müssen wir stellen um Lösungen für alle Wörter zu finden?
word([a, a, l]).
word([a, a, r]).
word([a, a, s]).
word([a, b, a]).
word([a, b, i]).
word([a, b, o]).
word([a, b, t]).
word([a, c, h]).
word([a, c, t]).
word([a, d, d]).
word([a, d, e]).
word([a, g, a]).
word([a, h, a]).
word([a, h, m]).
word([a, h, n]).
word([a, h, s]).
word([a, i, r]).
word([a, i, s]).
word([a, j, a]).
word([a, k, i]).
word([a, k, t]).
word([a, l, b]).
word([a, l, e]).
word([a, l, k]).
word([a, l, l]).
word([a, l, m]).
word([a, l, p]).
word([a, l, s]).
word([a, l, t]).
word([a, l, u]).
word([a, m, i]).
word([a, m, t]).
word([a, n, i]).
word([a, n, s]).
word([a, p, p]).
word([a, r, a]).
word([a, r, e]).
word([a, r, g]).
word([a, r, m]).
word([a, r, s]).
word([a, r, t]).
word([a, s, e]).
word([a, s, s]).
word([a, s, t]).
word([a, t, z]).
word([a, u, a]).
word([a, u, e]).
word([a, u, f]).
word([a, u, s]).
word([a, v, e]).
word([a, x, t]).
word([a, y, e]).
word([b, a, d]).
word([b, a, h]).
word([b, a, i]).
word([b, a, k]).
word([b, a, m]).
word([b, a, n]).
word([b, a, r]).
word([b, a, t]).
word([b, a, u]).
word([b, e, b]).
word([b, e, g]).
word([b, e, i]).
word([b, e, l]).
word([b, e, o]).
word([b, e, t]).
word([b, e, y]).
word([b, i, m]).
word([b, i, n]).
word([b, i, o]).
word([b, i, s]).
word([b, i, t]).
word([b, o, a]).
word([b, o, b]).
word([b, o, g]).
word([b, o, l]).
word([b, o, n]).
word([b, o, r]).
word([b, o, t]).
word([b, o, x]).
word([b, o, y]).
word([b, r, r]).
word([b, s, t]).
word([b, u, b]).
word([b, u, g]).
word([b, u, h]).
word([b, u, k]).
word([b, u, m]).
word([b, u, s]).
word([b, y, e]).
word([c, a, b]).
word([c, a, p]).
word([c, a, r]).
word([c, e, r]).
word([c, e, s]).
word([c, h, i]).
word([c, i, s]).
word([c, o, p]).
word([c, u, p]).
word([c, u, t]).
word([d, a, d]).
word([d, a, n]).
word([d, a, r]).
word([d, a, s]).
word([d, a, o]).
word([d, a, u]).
word([d, a, x]).
word([d, e, m]).
word([d, e, n]).
word([d, e, o]).
word([d, e, r]).
word([d, e, s]).
word([d, e, z]).
word([d, i, a]).
word([d, i, e]).
word([d, i, p]).
word([d, i, r]).
word([d, i, s]).
word([d, o, l]).
word([d, o, m]).
word([d, o, n]).
word([d, o, p]).
word([d, o, s]).
word([d, r, y]).
word([d, u, c]).
word([d, u, n]).
word([d, u, o]).
word([d, u, r]).
word([d, u, z]).
word([d, y, n]).
word([e, b, b]).
word([e, c, k]).
word([e, g, g]).
word([e, g, o]).
word([e, h, e]).
word([e, h, r]).
word([e, i, a]).
word([e, i, d]).
word([e, i, l]).
word([e, i, n]).
word([e, i, s]).
word([e, l, f]).
word([e, m, d]).
word([e, m, o]).
word([e, m, u]).
word([e, n, d]).
word([e, n, g]).
word([e, p, o]).
word([e, r, b]).
word([e, r, d]).
word([e, r, g]).
word([e, r, n]).
word([e, r, s]).
word([e, r, z]).
word([e, s, s]).
word([e, t, a]).
word([e, w, e]).
word([e, x, e]).
word([e, x, t]).
word([f, a, d]).
word([f, a, n]).
word([f, a, s]).
word([f, a, x]).
word([f, e, e]).
word([f, e, g]).
word([f, e, h]).
word([f, e, i]).
word([f, e, s]).
word([f, e, x]).
word([f, e, z]).
word([f, i, s]).
word([f, i, t]).
word([f, i, x]).
word([f, o, n]).
word([f, o, x]).
word([f, r, a]).
word([f, u, g]).
word([f, u, n]).
word([g, a, b]).
word([g, a, g]).
word([g, a, r]).
word([g, a, s]).
word([g, a, t]).
word([g, a, u]).
word([g, a, y]).
word([g, e, b]).
word([g, e, h]).
word([g, e, i]).
word([g, e, l]).
word([g, e, n]).
word([g, e, o]).
word([g, e, r]).
word([g, e, s]).
word([g, i, b]).
word([g, i, g]).
word([g, i, n]).
word([g, i, s]).
word([g, n, u]).
word([g, o, f]).
word([g, o, i]).
word([g, o, n]).
word([g, o, r]).
word([g, u, r]).
word([g, u, t]).
word([h, a, b]).
word([h, a, g]).
word([h, a, i]).
word([h, a, k]).
word([h, a, r]).
word([h, a, t]).
word([h, a, u]).
word([h, e, b]).
word([h, e, g]).
word([h, e, i]).
word([h, e, m]).
word([h, e, r]).
word([h, e, u]).
word([h, e, x]).
word([h, e, y]).
word([h, i, e]).
word([h, i, n]).
word([h, i, p]).
word([h, i, s]).
word([h, i, t]).
word([h, o, b]).
word([h, o, f]).
word([h, o, i]).
word([h, o, l]).
word([h, o, t]).
word([h, u, b]).
word([h, u, f]).
word([h, u, i]).
word([h, u, p]).
word([h, u, r]).
word([h, u, t]).
word([i, a, h]).
word([i, c, h]).
word([i, c, k]).
word([i, d, s]).
word([i, d, o]).
word([i, h, m]).
word([i, h, n]).
word([i, h, r]).
word([i, m, p]).
word([i, n, s]).
word([i, o, d]).
word([i, o, n]).
word([i, r, e]).
word([i, r, r]).
word([i, s, s]).
word([i, s, t]).
word([i, x, e]).
word([i, x, t]).
word([j, a, g]).
word([j, a, b]).
word([j, a, k]).
word([j, a, m]).
word([j, a, s]).
word([j, e, n]).
word([j, e, t]).
word([j, e, u]).
word([j, o, a]).
word([j, o, b]).
word([j, o, d]).
word([j, o, t]).
word([j, u, p]).
word([j, u, s]).
word([j, u, x]).
word([k, a, i]).
word([k, a, k]).
word([k, a, m]).
word([k, a, p]).
word([k, a, r]).
word([k, a, t]).
word([k, a, u]).
word([k, e, a]).
word([k, e, n]).
word([k, i, d]).
word([k, i, r]).
word([k, i, t]).
word([k, l, o]).
word([k, o, g]).
word([k, o, i]).
word([k, o, k]).
word([k, o, r]).
word([k, o, s]).
word([k, o, t]).
word([k, u, h]).
word([k, u, r]).
word([k, u, x]).
word([l, a, b]).
word([l, a, g]).
word([l, a, r]).
word([l, a, s]).
word([l, a, u]).
word([l, a, x]).
word([l, e, b]).
word([l, e, e]).
word([l, e, g]).
word([l, e, i]).
word([l, e, k]).
word([l, e, s]).
word([l, e, u]).
word([l, e, w]).
word([l, e, x]).
word([l, i, d]).
word([l, o, b]).
word([l, o, g]).
word([l, o, h]).
word([l, o, l]).
word([l, o, k]).
word([l, o, s]).
word([l, o, t]).
word([l, u, d]).
word([l, u, g]).
word([l, u, k]).
word([l, u, s]).
word([l, u, v]).
word([l, u, x]).
word([m, a, g]).
word([m, a, i]).
word([m, a, l]).
word([m, a, n]).
word([m, a, u]).
word([m, e, m]).
word([m, e, t]).
word([m, i, m]).
word([m, i, r]).
word([m, i, t]).
word([m, i, x]).
word([m, m, h]).
word([m, o, a]).
word([m, o, b]).
word([m, o, l]).
word([m, o, p]).
word([m, o, x]).
word([m, u, d]).
word([m, u, h]).
word([m, u, m]).
word([m, u, r]).
word([m, u, s]).
word([m, u, t]).
word([m, y, s]).
word([n, a, g]).
word([n, a, h]).
word([n, e, e]).
word([n, e, u]).
word([n, e, t]).
word([n, i, d]).
word([n, i, e]).
word([n, i, x]).
word([n, o, n]).
word([n, o, t]).
word([n, u, n]).
word([n, u, r]).
word([n, u, s]).
word([n, u, t]).
word([n, y, s]).
word([o, b, i]).
word([o, c, h]).
word([o, d, e]).
word([o, d, s]).
word([o, f, f]).
word([o, f, t]).
word([o, h, a]).
word([o, h, m]).
word([o, h, o]).
word([o, h, r]).
word([o, i, e]).
word([o, j, e]).
word([o, l, é]).
word([o, l, l]).
word([o, l, m]).
word([o, m, a]).
word([o, m, i]).
word([o, n, s]).
word([o, p, a]).
word([o, p, i]).
word([o, r, t]).
word([o, s, t]).
word([o, r, k]).
word([o, u, d]).
word([o, u, t]).
word([p, a, h]).
word([p, a, d]).
word([p, a, k]).
word([p, a, l]).
word([p, a, n]).
word([p, a, r]).
word([p, a, s]).
word([p, a, x]).
word([p, e, p]).
word([p, e, r]).
word([p, e, s]).
word([p, h, i]).
word([p, i, k]).
word([p, i, n]).
word([p, i, s]).
word([p, i, z]).
word([p, l, i]).
word([p, o, f]).
word([p, o, l]).
word([p, o, p]).
word([p, o, s]).
word([p, o, t]).
word([p, r, o]).
word([p, s, i]).
word([p, s, t]).
word([p, u, b]).
word([p, u, d]).
word([p, u, h]).
word([p, u, l]).
word([p, u, p]).
word([p, u, r]).
word([p, y, a]).
word([q, i, s]).
word([q, u, a]).
word([r, a, d]).
word([r, a, g]).
word([r, a, h]).
word([r, a, i]).
word([r, a, n]).
word([r, a, p]).
word([r, a, r]).
word([r, a, s]).
word([r, a, t]).
word([r, a, u]).
word([r, e, d]).
word([r, e, e]).
word([r, e, g]).
word([r, e, h]).
word([r, e, n]).
word([r, e, p]).
word([r, e, s]).
word([r, e, u]).
word([r, e, x]).
word([r, h, e]).
word([r, h, o]).
word([r, o, d]).
word([r, o, h]).
word([r, o, i]).
word([r, o, m]).
word([r, o, t]).
word([r, u, f]).
word([r, u, h]).
word([r, u, m]).
word([r, u, n]).
word([r, u, s]).
word([r, y, e]).
word([s, a, g]).
word([s, a, h]).
word([s, a, m]).
word([s, a, u]).
word([s, a, x]).
word([s, e, c]).
word([s, e, e]).
word([s, e, h]).
word([s, e, i]).
word([s, e, m]).
word([s, e, n]).
word([s, e, t]).
word([s, e, x]).
word([s, i, c]).
word([s, i, e]).
word([s, i, r]).
word([s, k, i]).
word([s, k, a]).
word([s, o, d]).
word([s, o, g]).
word([s, o, l]).
word([s, o, u]).
word([s, p, a]).
word([s, u, d]).
word([s, u, r]).
word([t, a, b]).
word([t, a, g]).
word([t, a, i]).
word([t, a, l]).
word([t, a, o]).
word([t, a, t]).
word([t, a, u]).
word([t, e, e]).
word([t, e, x]).
word([t, i, c]).
word([t, i, p]).
word([t, j, a]).
word([t, o, b]).
word([t, o, d]).
word([t, o, n]).
word([t, o, p]).
word([t, o, r]).
word([t, o, s]).
word([t, o, t]).
word([t, u, e]).
word([t, u, n]).
word([t, u, t]).
word([t, y, p]).
word([u, d, s]).
word([u, f, f]).
word([u, f, o]).
word([u, h, r]).
word([u, h, u]).
word([u, l, k]).
word([u, l, m]).
word([u, m, s]).
word([u, n, d]).
word([u, n, i]).
word([u, n, k]).
word([u, n, s]).
word([u, p, s]).
word([u, r, e]).
word([u, r, s]).
word([u, s, o]).
word([u, z, e]).
word([u, z, t]).
word([v, a, g]).
word([v, a, n]).
word([v, i, a]).
word([v, i, f]).
word([v, o, m]).
word([v, o, n]).
word([v, o, r]).
word([w, a, d]).
word([w, a, g]).
word([w, a, l]).
word([w, a, r]).
word([w, a, s]).
word([w, a, t]).
word([w, a, u]).
word([w, e, b]).
word([w, e, g]).
word([w, e, h]).
word([w, e, m]).
word([w, e, n]).
word([w, e, r]).
word([w, e, s]).
word([w, i, e]).
word([w, i, r]).
word([w, o, b]).
word([w, o, g]).
word([w, o, k]).
word([w, o, n]).
word([w, o, w]).
word([w, u, t]).
word([x, i, s]).
word([y, a, k]).
word([y, e, n]).
word([y, i, n]).
word([z, a, g]).
word([z, a, r]).
word([z, e, a]).
word([z, e, h]).
word([z, e, n]).
word([z, e, r]).
word([z, i, g]).
word([z, o, g]).
word([z, o, n]).
word([z, o, o]).
word([z, o, t]).
word([z, u, g]).
word([z, u, m]).
word([z, u, r]).
word([z, w, o]).
word([a, b, e, r]).
word([a, c, h, s]).
word([a, c, h, t]).
word([a, d, e, l]).
word([a, d, e, r]).
word([a, f, f, e]).
word([a, g, i, l]).
word([a, g, i, o]).
word([a, h, l, e]).
word([a, h, o, i]).
word([a, i, d, s]).
word([a, k, k, u]).
word([a, k, n, e]).
word([a, k, u, t]).
word([a, l, g, e]).
word([a, l, s, o]).
word([a, m, m, e]).
word([a, m, o, k]).
word([a, m, o, r]).
word([a, m, t, s]).
word([a, n, a, l]).
word([a, n, i, s]).
word([a, n, t, i]).
word([a, r, i, d]).
word([a, r, i, e]).
word([a, r, z, t]).
word([a, s, y, l]).
word([a, t, e, m]).
word([a, t, o, m]).
word([a, u, c, h]).
word([a, u, l, a]).
word([a, u, r, a]).
word([a, u, t, o]).
word([a, z, u, r]).
word([b, a, b, y]).
word([b, a, c, h]).
word([b, a, c, k]).
word([b, a, d, e]).
word([b, a, h, n]).
word([b, a, l, d]).
word([b, a, l, l]).
word([b, a, l, z]).
word([b, a, n, d]).
word([b, a, n, g]).
word([b, a, n, k]).
word([b, a, n, n]).
word([b, a, r, g]).
word([b, a, r, k]).
word([b, a, r, t]).
word([b, a, s, e]).
word([b, a, s, s]).
word([b, a, s, t]).
word([b, a, u, m]).
word([b, e, a, t]).
word([b, e, e, t]).
word([b, e, i, l]).
word([b, e, i, m]).
word([b, e, i, n]).
word([b, e, r, g]).
word([b, e, t, t]).
word([b, i, e, r]).
word([b, i, l, d]).
word([b, i, s, s]).
word([b, i, s, t]).
word([b, l, a, s]).
word([b, l, a, u]).
word([b, l, e, i]).
word([b, l, u, t]).
word([b, o, c, k]).
word([b, o, h, r]).
word([b, o, j, e]).
word([b, o, n, d]).
word([b, o, n, i]).
word([b, o, o, m]).
word([b, o, o, t]).
word([b, o, r, d]).
word([b, o, s, s]).
word([b, o, t, e]).
word([b, r, a, t]).
word([b, r, a, u]).
word([b, r, a, v]).
word([b, r, e, i]).
word([b, r, i, e]).
word([b, r, o, t]).
word([b, r, u, t]).
word([b, u, c, h]).
word([b, u, d, e]).
word([b, u, n, d]).
word([b, u, n, t]).
word([b, u, r, g]).
word([c, a, f, é]).
word([c, e, n, t]).
word([c, h, a, t]).
word([c, h, e, f]).
word([c, h, i, c]).
word([c, h, i, p]).
word([c, h, o, r]).
word([c, l, o, u]).
word([c, l, u, b]).
word([c, o, d, e]).
word([c, o, u, p]).
word([d, a, c, h]).
word([d, a, m, e]).
word([d, a, m, m]).
word([d, a, n, k]).
word([d, a, n, n]).
word([d, a, r, m]).
word([d, a, s, s]).
word([d, a, t, o]).
word([d, a, z, u]).
word([d, e, c, k]).
word([d, e, i, n]).
word([d, e, m, o]).
word([d, e, n, k]).
word([d, e, p, p]).
word([d, e, r, b]).
word([d, e, u, t]).
word([d, i, c, h]).
word([d, i, c, k]).
word([d, i, e, b]).
word([d, i, e, s]).
word([d, i, l, l]).
word([d, i, n, g]).
word([d, i, t, o]).
word([d, i, v, a]).
word([d, o, c, h]).
word([d, o, c, k]).
word([d, o, g, e]).
word([d, o, o, f]).
word([d, o, r, f]).
word([d, o, r, n]).
word([d, o, r, t]).
word([d, o, s, e]).
word([d, r, a, n]).
word([d, r, e, h]).
word([d, r, e, i]).
word([d, r, i, n]).
word([d, r, o, h]).
word([d, u, a, l]).
word([d, u, f, t]).
word([d, u, m, m]).
word([d, u, n, g]).
word([d, u, t, t]).
word([e, b, b, e]).
word([e, b, e, n]).
word([e, b, e, r]).
word([e, c, h, o]).
word([e, c, h, t]).
word([e, c, k, e]).
word([e, d, e, l]).
word([e, d, e, n]).
word([e, f, e, u]).
word([e, g, a, l]).
word([e, g, e, l]).
word([e, g, g, e]).
word([e, h, e, r]).
word([e, h, r, e]).
word([e, i, b, e]).
word([e, i, c, h]).
word([e, i, e, r]).
word([e, i, e, s]).
word([e, i, n, s]).
word([e, k, e, l]).
word([e, l, a, n]).
word([e, l, c, h]).
word([e, l, f, e]).
word([e, l, f, t]).
word([e, l, l, e]).
word([e, n, d, e]).
word([e, n, g, e]).
word([e, n, t, e]).
word([e, p, e, n]).
word([e, p, o, s]).
word([e, r, b, e]).
word([e, r, d, e]).
word([e, r, l, e]).
word([e, r, s, t]).
word([e, s, e, l]).
word([e, t, a, t]).
word([e, t, u, i]).
word([e, t, w, a]).
word([e, u, c, h]).
word([e, u, e, r]).
word([e, u, l, e]).
word([e, u, r, o]).
word([e, w, i, g]).
word([e, x, i, l]).
word([e, x, o, t]).
word([f, a, c, h]).
word([f, a, d, e]).
word([f, a, h, l]).
word([f, a, h, r]).
word([f, a, k, t]).
word([f, a, l, b]).
word([f, a, l, l]).
word([f, a, l, t]).
word([f, a, l, z]).
word([f, a, n, d]).
word([f, a, n, g]).
word([f, a, r, b]).
word([f, a, r, m]).
word([f, a, r, n]).
word([f, a, s, s]).
word([f, a, s, t]).
word([f, a, t, a]).
word([f, a, u, l]).
word([f, a, u, n]).
word([f, e, h, l]).
word([f, e, i, g]).
word([f, e, i, l]).
word([f, e, i, n]).
word([f, e, l, d]).
word([f, e, l, l]).
word([f, e, l, s]).
word([f, e, r, n]).
word([f, e, s, t]).
word([f, e, t, t]).
word([f, i, c, k]).
word([f, i, e, l]).
word([f, i, e, s]).
word([f, i, l, m]).
word([f, i, l, z]).
word([f, i, n, g]).
word([f, i, n, k]).
word([f, l, a, u]).
word([f, l, o, g]).
word([f, l, o, h]).
word([f, l, u, g]).
word([f, l, u, r]).
word([f, l, u, t]).
word([f, o, n, d]).
word([f, o, r, m]).
word([f, o, r, t]).
word([f, o, t, o]).
word([f, r, a, u]).
word([f, r, e, i]).
word([f, r, o, h]).
word([f, r, o, n]).
word([f, r, o, r]).
word([f, u, h, r]).
word([f, u, n, d]).
word([f, u, n, k]).
word([f, u, r, t]).
word([f, u, r, z]).
word([g, a, b, e]).
word([g, a, l, a]).
word([g, a, l, t]).
word([g, a, n, g]).
word([g, a, n, s]).
word([g, a, n, z]).
word([g, a, r, n]).
word([g, a, s, t]).
word([g, a, u, l]).
word([g, a, z, e]).
word([g, e, c, k]).
word([g, e, i, l]).
word([g, e, i, z]).
word([g, e, l, b]).
word([g, e, l, d]).
word([g, e, r, n]).
word([g, i, b, t]).
word([g, i, e, r]).
word([g, i, f, t]).
word([g, i, n, g]).
word([g, i, p, s]).
word([g, i, r, o]).
word([g, l, a, s]).
word([g, l, u, t]).
word([g, n, o, m]).
word([g, o, l, d]).
word([g, o, l, f]).
word([g, o, n, g]).
word([g, o, s, s]).
word([g, o, t, t]).
word([g, r, a, b]).
word([g, r, a, d]).
word([g, r, a, f]).
word([g, r, a, l]).
word([g, r, a, s]).
word([g, r, a, t]).
word([g, r, a, u]).
word([g, r, o, b]).
word([g, r, o, g]).
word([g, r, o, s]).
word([g, r, u, b]).
word([g, u, c, k]).
word([g, u, r, t]).
word([g, u, r, u]).
word([g, u, s, s]).
word([g, u, t, s]).
word([h, a, a, r]).
word([h, a, b, e]).
word([h, a, c, k]).
word([h, a, f, t]).
word([h, a, h, n]).
word([h, a, i, n]).
word([h, a, l, b]).
word([h, a, l, f]).
word([h, a, l, l]).
word([h, a, l, m]).
word([h, a, l, s]).
word([h, a, l, t]).
word([h, a, n, d]).
word([h, a, n, f]).
word([h, a, n, g]).
word([h, a, r, n]).
word([h, a, r, t]).
word([h, a, r, z]).
word([h, a, s, e]).
word([h, a, s, s]).
word([h, a, u, s]).
word([h, a, u, t]).
word([h, e, c, k]).
word([h, e, e, r]).
word([h, e, f, e]).
word([h, e, f, t]).
word([h, e, h, l]).
word([h, e, i, l]).
word([h, e, i, m]).
word([h, e, i, z]).
word([h, e, l, d]).
word([h, e, l, l]).
word([h, e, l, m]).
word([h, e, m, d]).
word([h, e, r, b]).
word([h, e, r, d]).
word([h, e, r, r]).
word([h, e, r, z]).
word([h, e, t, z]).
word([h, e, x, e]).
word([h, i, e, b]).
word([h, i, e, r]).
word([h, i, n, g]).
word([h, i, r, n]).
word([h, o, c, h]).
word([h, o, h, e]).
word([h, o, h, l]).
word([h, o, h, n]).
word([h, o, l, d]).
word([h, o, l, m]).
word([h, o, l, z]).
word([h, o, r, n]).
word([h, o, r, t]).
word([h, o, s, e]).
word([h, u, h, n]).
word([h, u, n, d]).
word([h, u, p, e]).
word([h, u, r, e]).
word([i, d, e, e]).
word([i, d, o, l]).
word([i, g, e, l]).
word([i, m, p, f]).
word([i, n, f, o]).
word([i, n, k, a]).
word([i, n, n, e]).
word([i, s, s, t]).
word([j, a, g, d]).
word([j, a, h, r]).
word([j, a, z, z]).
word([j, e, d, e]).
word([j, e, e, p]).
word([j, e, n, e]).
word([j, o, c, h]).
word([j, o, g, a]).
word([j, o, t, a]).
word([j, u, d, e]).
word([j, u, d, o]).
word([j, u, l, i]).
word([j, u, n, g]).
word([j, u, n, i]).
word([j, u, r, a]).
word([j, u, s, t]).
word([j, u, t, e]).
word([k, a, d, i]).
word([k, a, f, f]).
word([k, a, h, l]).
word([k, a, h, n]).
word([k, a, l, b]).
word([k, a, l, i]).
word([k, a, l, k]).
word([k, a, l, t]).
word([k, a, m, m]).
word([k, a, n, u]).
word([k, a, r, g]).
word([k, a, r, o]).
word([k, a, t, z]).
word([k, a, u, f]).
word([k, a, u, m]).
word([k, a, u, z]).
word([k, e, c, k]).
word([k, e, h, r]).
word([k, e, i, l]).
word([k, e, i, m]).
word([k, e, i, n]).
word([k, e, k, s]).
word([k, e, n, n]).
word([k, e, r, l]).
word([k, e, r, n]).
word([k, e, s, s]).
word([k, i, e, l]).
word([k, i, e, s]).
word([k, i, l, o]).
word([k, i, m, m]).
word([k, i, n, d]).
word([k, i, n, n]).
word([k, i, n, o]).
word([k, i, p, p]).
word([k, i, t, a]).
word([k, i, t, t]).
word([k, l, a, r]).
word([k, l, a, u]).
word([k, l, e, b]).
word([k, l, e, e]).
word([k, l, u, b]).
word([k, l, u, g]).
word([k, n, e, t]).
word([k, n, i, e]).
word([k, o, c, h]).
word([k, o, h, l]).
word([k, o, j, e]).
word([k, o, k, s]).
word([k, o, p, f]).
word([k, o, r, b]).
word([k, o, r, d]).
word([k, o, r, k]).
word([k, o, r, n]).
word([k, o, s, t]).
word([k, r, a, m]).
word([k, r, a, n]).
word([k, r, e, m]).
word([k, r, o, n]).
word([k, r, u, d]).
word([k, r, u, g]).
word([k, u, f, e]).
word([k, u, l, i]).
word([k, u, l, t]).
word([k, u, n, d]).
word([k, u, r, s]).
word([k, u, r, z]).
word([k, u, s, s]).
word([l, a, c, h]).
word([l, a, c, k]).
word([l, a, d, e]).
word([l, a, g, e]).
word([l, a, h, m]).
word([l, a, i, b]).
word([l, a, i, e]).
word([l, a, m, a]).
word([l, a, m, m]).
word([l, a, n, d]).
word([l, a, n, g]).
word([l, a, s, t]).
word([l, a, t, z]).
word([l, a, u, b]).
word([l, a, u, f]).
word([l, a, u, s]).
word([l, a, u, t]).
word([l, a, v, a]).
word([l, e, c, k]).
word([l, e, e, r]).
word([l, e, h, m]).
word([l, e, h, r]).
word([l, e, i, b]).
word([l, e, i, d]).
word([l, e, i, h]).
word([l, e, i, m]).
word([l, e, i, t]).
word([l, e, n, k]).
word([l, e, n, z]).
word([l, e, r, n]).
word([l, e, s, e]).
word([l, i, e, b]).
word([l, i, e, d]).
word([l, i, e, f]).
word([l, i, e, h]).
word([l, i, e, s]).
word([l, i, g, a]).
word([l, i, l, a]).
word([l, i, m, o]).
word([l, i, n, d]).
word([l, i, r, a]).
word([l, i, r, e]).
word([l, i, s, t]).
word([l, i, t, t]).
word([l, o, c, h]).
word([l, o, c, k]).
word([l, o, h, n]).
word([l, o, r, d]).
word([l, o, r, e]).
word([l, u, f, t]).
word([l, u, k, e]).
word([l, u, p, e]).
word([l, u, s, t]).
word([m, a, a, r]).
word([m, a, d, e]).
word([m, a, g, d]).
word([m, a, h, l]).
word([m, a, h, n]).
word([m, a, l, z]).
word([m, a, m, a]).
word([m, a, n, n]).
word([m, a, r, k]).
word([m, a, r, s]).
word([m, a, s, t]).
word([m, a, t, t]).
word([m, a, u, l]).
word([m, a, u, s]).
word([m, a, u, t]).
word([m, e, e, r]).
word([m, e, h, l]).
word([m, e, h, r]).
word([m, e, i, n]).
word([m, e, m, o]).
word([m, e, r, k]).
word([m, e, s, s]).
word([m, i, c, h]).
word([m, i, e, d]).
word([m, i, e, f]).
word([m, i, e, s]).
word([m, i, e, t]).
word([m, i, l, d]).
word([m, i, l, z]).
word([m, i, m, e]).
word([m, i, n, e]).
word([m, i, n, i]).
word([m, i, s, t]).
word([m, o, d, e]).
word([m, o, d, i]).
word([m, o, f, a]).
word([m, o, h, n]).
word([m, o, h, r]).
word([m, o, l, e]).
word([m, o, l, l]).
word([m, o, n, d]).
word([m, o, o, r]).
word([m, o, o, s]).
word([m, o, p, p]).
word([m, o, p, s]).
word([m, o, r, d]).
word([m, o, s, t]).
word([m, u, l, l]).
word([m, u, m, m]).
word([m, u, n, d]).
word([m, u, s, e]).
word([n, a, c, h]).
word([n, a, h, m]).
word([n, a, i, v]).
word([n, a, m, e]).
word([n, a, n, o]).
word([n, a, p, f]).
word([n, a, r, r]).
word([n, a, s, e]).
word([n, a, s, s]).
word([n, a, z, i]).
word([n, e, i, d]).
word([n, e, i, n]).
word([n, e, n, n]).
word([n, e, o, n]).
word([n, e, p, p]).
word([n, e, r, v]).
word([n, e, r, z]).
word([n, e, s, t]).
word([n, e, t, t]).
word([n, e, t, z]).
word([n, e, u, n]).
word([n, i, e, t]).
word([n, i, x, e]).
word([n, o, c, h]).
word([n, o, r, d]).
word([n, o, r, m]).
word([n, o, t, a]).
word([n, o, v, a]).
word([n, u, l, l]).
word([n, u, s, s]).
word([n, u, t, z]).
word([o, a, s, e]).
word([o, b, e, r]).
word([o, b, i, g]).
word([o, b, o, e]).
word([o, b, s, t]).
word([o, c, h, s]).
word([o, d, e, m]).
word([o, d, e, r]).
word([o, f, e, n]).
word([o, h, n, e]).
word([o, k, a, y]).
word([o, l, i, v]).
word([o, m, e, n]).
word([o, p, e, r]).
word([o, p, u, s]).
word([o, r, a, l]).
word([o, r, t, s]).
word([o, v, a, l]).
word([o, x, i, d]).
word([o, x, y, d]).
word([o, z, o, n]).
word([p, a, a, r]).
word([p, a, c, k]).
word([p, a, k, t]).
word([p, a, p, a]).
word([p, a, p, i]).
word([p, a, p, p]).
word([p, a, r, a]).
word([p, a, r, k]).
word([p, a, r, t]).
word([p, a, s, s]).
word([p, a, t, e]).
word([p, e, c, h]).
word([p, e, i, l]).
word([p, e, i, n]).
word([p, e, l, z]).
word([p, e, s, t]).
word([p, f, a, d]).
word([p, f, a, u]).
word([p, h, o, n]).
word([p, i, l, s]).
word([p, i, l, z]).
word([p, l, a, n]).
word([p, l, u, s]).
word([p, n, e, u]).
word([p, o, e, t]).
word([p, o, m, p]).
word([p, o, o, l]).
word([p, o, p, e]).
word([p, o, p, o]).
word([p, o, r, e]).
word([p, o, s, e]).
word([p, o, s, t]).
word([p, u, f, f]).
word([p, u, l, k]).
word([p, u, l, s]).
word([p, u, l, t]).
word([p, u, m, a]).
word([p, u, m, p]).
word([p, u, n, k]).
word([p, u, t, e]).
word([p, u, t, z]).
word([q, u, a, l]).
word([q, u, e, r]).
word([q, u, i, z]).
word([r, a, b, e]).
word([r, a, h, m]).
word([r, a, i, n]).
word([r, a, n, d]).
word([r, a, n, g]).
word([r, a, p, s]).
word([r, a, s, t]).
word([r, a, t, s]).
word([r, a, u, b]).
word([r, a, u, m]).
word([r, a, u, s]).
word([r, e, a, l]).
word([r, e, b, e]).
word([r, e, c, k]).
word([r, e, d, e]).
word([r, e, i, f]).
word([r, e, i, m]).
word([r, e, i, n]).
word([r, e, i, s]).
word([r, e, i, t]).
word([r, e, i, z]).
word([r, e, n, n]).
word([r, e, s, t]).
word([r, e, u, e]).
word([r, i, e, b]).
word([r, i, e, f]).
word([r, i, e, s]).
word([r, i, e, t]).
word([r, i, f, f]).
word([r, i, n, d]).
word([r, i, n, g]).
word([r, i, s, s]).
word([r, i, t, t]).
word([r, o, b, e]).
word([r, o, c, h]).
word([r, o, c, k]).
word([r, o, h, r]).
word([r, o, l, l]).
word([r, o, s, a]).
word([r, o, s, e]).
word([r, o, s, t]).
word([r, u, c, k]).
word([r, u, h, e]).
word([r, u, h, m]).
word([r, u, i, n]).
word([r, u, n, d]).
word([r, u, n, e]).
word([r, u, t, e]).
word([s, a, a, l]).
word([s, a, a, t]).
word([s, a, c, h]).
word([s, a, c, k]).
word([s, a, f, t]).
word([s, a, g, a]).
word([s, a, g, e]).
word([s, a, l, m]).
word([s, a, l, z]).
word([s, a, m, e]).
word([s, a, m, t]).
word([s, a, n, d]).
word([s, a, n, g]).
word([s, a, n, k]).
word([s, a, n, n]).
word([s, a, r, g]).
word([s, a, t, t]).
word([s, a, t, z]).
word([s, a, u, g]).
word([s, a, u, m]).
word([s, c, h, i]).
word([s, e, h, r]).
word([s, e, i, d]).
word([s, e, i, l]).
word([s, e, i, m]).
word([s, e, i, n]).
word([s, e, k, t]).
word([s, e, n, f]).
word([s, e, n, k]).
word([s, i, c, h]).
word([s, i, e, b]).
word([s, i, e, g]).
word([s, i, e, h]).
word([s, i, e, l]).
word([s, i, l, o]).
word([s, i, m, s]).
word([s, i, n, d]).
word([s, i, n, g]).
word([s, i, n, n]).
word([s, i, t, z]).
word([s, k, a, t]).
word([s, l, i, p]).
word([s, l, u, m]).
word([s, m, o, g]).
word([s, o, d, a]).
word([s, o, f, a]).
word([s, o, f, f]).
word([s, o, f, t]).
word([s, o, h, n]).
word([s, o, j, a]).
word([s, o, l, d]).
word([s, o, l, e]).
word([s, o, l, i]).
word([s, o, l, o]).
word([s, p, a, n]).
word([s, p, a, r]).
word([s, p, i, n]).
word([s, p, u, k]).
word([s, p, u, r]).
word([s, t, a, b]).
word([s, t, a, k]).
word([s, t, a, r]).
word([s, t, a, u]).
word([s, t, e, g]).
word([s, t, i, l]).
word([s, t, u, r]).
word([s, u, c, h]).
word([t, a, b, u]).
word([t, a, f, t]).
word([t, a, k, t]).
word([t, a, l, g]).
word([t, a, l, k]).
word([t, a, n, d]).
word([t, a, n, g]).
word([t, a, n, k]).
word([t, a, n, z]).
word([t, a, r, a]).
word([t, a, r, n]).
word([t, a, u, b]).
word([t, a, u, f]).
word([t, a, x, i]).
word([t, e, a, m]).
word([t, e, e, r]).
word([t, e, i, g]).
word([t, e, i, l]).
word([t, e, l, e]).
word([t, e, r, z]).
word([t, e, s, t]).
word([t, e, x, t]).
word([t, h, o, r]).
word([t, i, c, k]).
word([t, i, e, f]).
word([t, i, e, r]).
word([t, i, p, p]).
word([t, o, f, u]).
word([t, o, l, l]).
word([t, o, p, f]).
word([t, o, p, p]).
word([t, o, r, f]).
word([t, o, t, e]).
word([t, o, t, o]).
word([t, o, u, r]).
word([t, r, a, b]).
word([t, r, a, f]).
word([t, r, a, g]).
word([t, r, a, n]).
word([t, r, a, t]).
word([t, r, e, t]).
word([t, r, e, u]).
word([t, r, i, o]).
word([t, r, i, p]).
word([t, r, o, g]).
word([t, r, u, g]).
word([t, u, b, e]).
word([t, u, c, h]).
word([t, u, f, f]).
word([t, u, r, m]).
word([t, u, r, n]).
word([u, f, e, r]).
word([u, k, a, s]).
word([u, l, m, e]).
word([u, m, s, o]).
word([u, n, k, e]).
word([u, n, z, e]).
word([u, r, a, n]).
word([u, r, i, g]).
word([u, r, i, n]).
word([u, r, n, e]).
word([v, a, m, p]).
word([v, a, s, e]).
word([v, a, t, i]).
word([v, e, n, e]).
word([v, e, r, b]).
word([v, e, r, s]).
word([v, e, t, o]).
word([v, i, e, h]).
word([v, i, e, l]).
word([v, i, e, r]).
word([v, i, s, a]).
word([v, i, z, e]).
word([v, o, g, t]).
word([v, o, l, k]).
word([v, o, l, l]).
word([v, o, l, t]).
word([v, o, r, m]).
word([v, o, r, n]).
word([w, a, b, e]).
word([w, a, c, h]).
word([w, a, d, e]).
word([w, a, d, i]).
word([w, a, h, l]).
word([w, a, h, n]).
word([w, a, h, r]).
word([w, a, l, d]).
word([w, a, l, l]).
word([w, a, l, z]).
word([w, a, m, s]).
word([w, a, n, d]).
word([w, a, n, n]).
word([w, a, r, b]).
word([w, a, r, d]).
word([w, a, r, e]).
word([w, a, r, f]).
word([w, a, r, m]).
word([w, a, r, n]).
word([w, a, r, t]).
word([w, a, t, t]).
word([w, e, h, e]).
word([w, e, h, r]).
word([w, e, i, b]).
word([w, e, i, h]).
word([w, e, i, l]).
word([w, e, i, n]).
word([w, e, i, t]).
word([w, e, l, k]).
word([w, e, l, l]).
word([w, e, l, t]).
word([w, e, r, k]).
word([w, e, r, t]).
word([w, e, s, t]).
word([w, e, t, t]).
word([w, e, t, z]).
word([w, i, c, h]).
word([w, i, e, s]).
word([w, i, l, d]).
word([w, i, n, d]).
word([w, i, n, k]).
word([w, i, r, d]).
word([w, i, r, r]).
word([w, i, r, t]).
word([w, i, t, z]).
word([w, o, g, e]).
word([w, o, h, l]).
word([w, o, h, n]).
word([w, o, l, f]).
word([w, o, l, l]).
word([w, o, r, t]).
word([w, o, z, u]).
word([w, u, n, d]).
word([w, u, r, f]).
word([w, u, r, m]).
word([w, u, s, t]).
word([y, e, t, i]).
word([y, o, g, a]).
word([z, a, h, l]).
word([z, a, h, m]).
word([z, a, h, n]).
word([z, a, n, k]).
word([z, a, p, f]).
word([z, a, r, t]).
word([z, a, u, m]).
word([z, a, u, n]).
word([z, e, h, n]).
word([z, e, i, t]).
word([z, e, l, l]).
word([z, e, l, t]).
word([z, e, u, g]).
word([z, i, e, l]).
word([z, i, e, r]).
word([z, i, m, t]).
word([z, i, n, k]).
word([z, i, n, n]).
word([z, i, n, s]).
word([z, o, f, e]).
word([z, o, f, f]).
word([z, o, l, l]).
word([z, o, n, e]).
word([z, o, p, f]).
word([z, o, r, n]).
word([z, o, t, e]).
word([z, u, p, f]).
word([z, w, a, r]).
word([z, w, e, i]).
