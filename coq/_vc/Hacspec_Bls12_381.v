(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t × fp_t × bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t × fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t × fp2_t × bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t × fp2_t × fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t × fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_1381 : fp_t) : fp2_t :=
  (n_1381, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_1382 : fp2_t) : fp2_t :=
  let '(n1_1383, n2_1384) :=
    n_1382 in 
  ((nat_mod_zero ) -% (n1_1383), (nat_mod_zero ) -% (n2_1384)).

Definition fp2add (n_1385 : fp2_t) (m_1386 : fp2_t) : fp2_t :=
  let '(n1_1387, n2_1388) :=
    n_1385 in 
  let '(m1_1389, m2_1390) :=
    m_1386 in 
  ((n1_1387) +% (m1_1389), (n2_1388) +% (m2_1390)).

Definition fp2sub (n_1391 : fp2_t) (m_1392 : fp2_t) : fp2_t :=
  fp2add (n_1391) (fp2neg (m_1392)).

Definition fp2mul (n_1393 : fp2_t) (m_1394 : fp2_t) : fp2_t :=
  let '(n1_1395, n2_1396) :=
    n_1393 in 
  let '(m1_1397, m2_1398) :=
    m_1394 in 
  let x1_1399 : fp_t :=
    ((n1_1395) *% (m1_1397)) -% ((n2_1396) *% (m2_1398)) in 
  let x2_1400 : fp_t :=
    ((n1_1395) *% (m2_1398)) +% ((n2_1396) *% (m1_1397)) in 
  (x1_1399, x2_1400).

Definition fp2inv (n_1401 : fp2_t) : fp2_t :=
  let '(n1_1402, n2_1403) :=
    n_1401 in 
  let t0_1404 : fp_t :=
    ((n1_1402) *% (n1_1402)) +% ((n2_1403) *% (n2_1403)) in 
  let t1_1405 : fp_t :=
    nat_mod_inv (t0_1404) in 
  let x1_1406 : fp_t :=
    (n1_1402) *% (t1_1405) in 
  let x2_1407 : fp_t :=
    (nat_mod_zero ) -% ((n2_1403) *% (t1_1405)) in 
  (x1_1406, x2_1407).

Definition fp2conjugate (n_1408 : fp2_t) : fp2_t :=
  let '(n1_1409, n2_1410) :=
    n_1408 in 
  (n1_1409, (nat_mod_zero ) -% (n2_1410)).

Definition fp6fromfp2 (n_1411 : fp2_t) : fp6_t :=
  (n_1411, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_1412 : fp6_t) : fp6_t :=
  let '(n1_1413, n2_1414, n3_1415) :=
    n_1412 in 
  (
    fp2sub (fp2zero ) (n1_1413),
    fp2sub (fp2zero ) (n2_1414),
    fp2sub (fp2zero ) (n3_1415)
  ).

Definition fp6add (n_1416 : fp6_t) (m_1417 : fp6_t) : fp6_t :=
  let '(n1_1418, n2_1419, n3_1420) :=
    n_1416 in 
  let '(m1_1421, m2_1422, m3_1423) :=
    m_1417 in 
  (
    fp2add (n1_1418) (m1_1421),
    fp2add (n2_1419) (m2_1422),
    fp2add (n3_1420) (m3_1423)
  ).

Definition fp6sub (n_1424 : fp6_t) (m_1425 : fp6_t) : fp6_t :=
  fp6add (n_1424) (fp6neg (m_1425)).

Definition fp6mul (n_1426 : fp6_t) (m_1427 : fp6_t) : fp6_t :=
  let '(n1_1428, n2_1429, n3_1430) :=
    n_1426 in 
  let '(m1_1431, m2_1432, m3_1433) :=
    m_1427 in 
  let eps_1434 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1435 : (fp_t × fp_t) :=
    fp2mul (n1_1428) (m1_1431) in 
  let t2_1436 : (fp_t × fp_t) :=
    fp2mul (n2_1429) (m2_1432) in 
  let t3_1437 : (fp_t × fp_t) :=
    fp2mul (n3_1430) (m3_1433) in 
  let t4_1438 : (fp_t × fp_t) :=
    fp2mul (fp2add (n2_1429) (n3_1430)) (fp2add (m2_1432) (m3_1433)) in 
  let t5_1439 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1438) (t2_1436)) (t3_1437) in 
  let x_1440 : (fp_t × fp_t) :=
    fp2add (fp2mul (t5_1439) (eps_1434)) (t1_1435) in 
  let t4_1441 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1428) (n2_1429)) (fp2add (m1_1431) (m2_1432)) in 
  let t5_1442 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1441) (t1_1435)) (t2_1436) in 
  let y_1443 : (fp_t × fp_t) :=
    fp2add (t5_1442) (fp2mul (eps_1434) (t3_1437)) in 
  let t4_1444 : (fp_t × fp_t) :=
    fp2mul (fp2add (n1_1428) (n3_1430)) (fp2add (m1_1431) (m3_1433)) in 
  let t5_1445 : (fp_t × fp_t) :=
    fp2sub (fp2sub (t4_1444) (t1_1435)) (t3_1437) in 
  let z_1446 : (fp_t × fp_t) :=
    fp2add (t5_1445) (t2_1436) in 
  (x_1440, y_1443, z_1446).

Definition fp6inv (n_1447 : fp6_t) : fp6_t :=
  let '(n1_1448, n2_1449, n3_1450) :=
    n_1447 in 
  let eps_1451 : (fp_t × fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1452 : (fp_t × fp_t) :=
    fp2mul (n1_1448) (n1_1448) in 
  let t2_1453 : (fp_t × fp_t) :=
    fp2mul (n2_1449) (n2_1449) in 
  let t3_1454 : (fp_t × fp_t) :=
    fp2mul (n3_1450) (n3_1450) in 
  let t4_1455 : (fp_t × fp_t) :=
    fp2mul (n1_1448) (n2_1449) in 
  let t5_1456 : (fp_t × fp_t) :=
    fp2mul (n1_1448) (n3_1450) in 
  let t6_1457 : (fp_t × fp_t) :=
    fp2mul (n2_1449) (n3_1450) in 
  let x0_1458 : (fp_t × fp_t) :=
    fp2sub (t1_1452) (fp2mul (eps_1451) (t6_1457)) in 
  let y0_1459 : (fp_t × fp_t) :=
    fp2sub (fp2mul (eps_1451) (t3_1454)) (t4_1455) in 
  let z0_1460 : (fp_t × fp_t) :=
    fp2sub (t2_1453) (t5_1456) in 
  let t0_1461 : (fp_t × fp_t) :=
    fp2mul (n1_1448) (x0_1458) in 
  let t0_1462 : (fp_t × fp_t) :=
    fp2add (t0_1461) (fp2mul (eps_1451) (fp2mul (n3_1450) (y0_1459))) in 
  let t0_1463 : (fp_t × fp_t) :=
    fp2add (t0_1462) (fp2mul (eps_1451) (fp2mul (n2_1449) (z0_1460))) in 
  let t0_1464 : (fp_t × fp_t) :=
    fp2inv (t0_1463) in 
  let x_1465 : (fp_t × fp_t) :=
    fp2mul (x0_1458) (t0_1464) in 
  let y_1466 : (fp_t × fp_t) :=
    fp2mul (y0_1459) (t0_1464) in 
  let z_1467 : (fp_t × fp_t) :=
    fp2mul (z0_1460) (t0_1464) in 
  (x_1465, y_1466, z_1467).

Definition fp12fromfp6 (n_1468 : fp6_t) : fp12_t :=
  (n_1468, fp6zero ).

Definition fp12neg (n_1469 : fp12_t) : fp12_t :=
  let '(n1_1470, n2_1471) :=
    n_1469 in 
  (fp6sub (fp6zero ) (n1_1470), fp6sub (fp6zero ) (n2_1471)).

Definition fp12add (n_1472 : fp12_t) (m_1473 : fp12_t) : fp12_t :=
  let '(n1_1474, n2_1475) :=
    n_1472 in 
  let '(m1_1476, m2_1477) :=
    m_1473 in 
  (fp6add (n1_1474) (m1_1476), fp6add (n2_1475) (m2_1477)).

Definition fp12sub (n_1478 : fp12_t) (m_1479 : fp12_t) : fp12_t :=
  fp12add (n_1478) (fp12neg (m_1479)).

Definition fp12mul (n_1480 : fp12_t) (m_1481 : fp12_t) : fp12_t :=
  let '(n1_1482, n2_1483) :=
    n_1480 in 
  let '(m1_1484, m2_1485) :=
    m_1481 in 
  let gamma_1486 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1487 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1482) (m1_1484) in 
  let t2_1488 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1483) (m2_1485) in 
  let x_1489 : (fp2_t × fp2_t × fp2_t) :=
    fp6add (t1_1487) (fp6mul (t2_1488) (gamma_1486)) in 
  let y_1490 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (fp6add (n1_1482) (n2_1483)) (fp6add (m1_1484) (m2_1485)) in 
  let y_1491 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (fp6sub (y_1490) (t1_1487)) (t2_1488) in 
  (x_1489, y_1491).

Definition fp12inv (n_1492 : fp12_t) : fp12_t :=
  let '(n1_1493, n2_1494) :=
    n_1492 in 
  let gamma_1495 : (fp2_t × fp2_t × fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1496 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1493) (n1_1493) in 
  let t2_1497 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n2_1494) (n2_1494) in 
  let t1_1498 : (fp2_t × fp2_t × fp2_t) :=
    fp6sub (t1_1496) (fp6mul (gamma_1495) (t2_1497)) in 
  let t2_1499 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (t1_1498) in 
  let x_1500 : (fp2_t × fp2_t × fp2_t) :=
    fp6mul (n1_1493) (t2_1499) in 
  let y_1501 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (fp6mul (n2_1494) (t2_1499)) in 
  (x_1500, y_1501).

Definition fp12exp (n_1502 : fp12_t) (k_1503 : scalar_t) : fp12_t :=
  let c_1504 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_1504 :=
    foldi (usize 0) (usize 256) (fun i_1505 c_1504 =>
      let c_1504 :=
        fp12mul (c_1504) (c_1504) in 
      let '(c_1504) :=
        if nat_mod_bit (k_1503) ((usize 255) - (i_1505)):bool then (
          let c_1504 :=
            fp12mul (c_1504) (n_1502) in 
          (c_1504)) else ((c_1504)) in 
      (c_1504))
    c_1504 in 
  c_1504.

Definition fp12conjugate (n_1506 : fp12_t) : fp12_t :=
  let '(n1_1507, n2_1508) :=
    n_1506 in 
  (n1_1507, fp6neg (n2_1508)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_1509 : g1_t) (q_1510 : g1_t) : g1_t :=
  let '(x1_1511, y1_1512, _) :=
    p_1509 in 
  let '(x2_1513, y2_1514, _) :=
    q_1510 in 
  let x_diff_1515 : fp_t :=
    (x2_1513) -% (x1_1511) in 
  let y_diff_1516 : fp_t :=
    (y2_1514) -% (y1_1512) in 
  let xovery_1517 : fp_t :=
    (y_diff_1516) *% (nat_mod_inv (x_diff_1515)) in 
  let x3_1518 : fp_t :=
    ((nat_mod_exp (xovery_1517) (@repr WORDSIZE32 2)) -% (x1_1511)) -% (
      x2_1513) in 
  let y3_1519 : fp_t :=
    ((xovery_1517) *% ((x1_1511) -% (x3_1518))) -% (y1_1512) in 
  (x3_1518, y3_1519, false).

Definition g1double_a (p_1520 : g1_t) : g1_t :=
  let '(x1_1521, y1_1522, _) :=
    p_1520 in 
  let x12_1523 : fp_t :=
    nat_mod_exp (x1_1521) (@repr WORDSIZE32 2) in 
  let xovery_1524 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_1523)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_1522))) in 
  let x3_1525 : fp_t :=
    (nat_mod_exp (xovery_1524) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_1521)) in 
  let y3_1526 : fp_t :=
    ((xovery_1524) *% ((x1_1521) -% (x3_1525))) -% (y1_1522) in 
  (x3_1525, y3_1526, false).

Definition g1double (p_1527 : g1_t) : g1_t :=
  let '(x1_1528, y1_1529, inf1_1530) :=
    p_1527 in 
  (if (((y1_1529) !=.? (nat_mod_zero )) && (negb (inf1_1530))):bool then (
      g1double_a (p_1527)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_1531 : g1_t) (q_1532 : g1_t) : g1_t :=
  let '(x1_1533, y1_1534, inf1_1535) :=
    p_1531 in 
  let '(x2_1536, y2_1537, inf2_1538) :=
    q_1532 in 
  (if (inf1_1535):bool then (q_1532) else ((if (inf2_1538):bool then (
          p_1531) else ((if ((p_1531) =.? (q_1532)):bool then (g1double (
                p_1531)) else ((if (negb (((x1_1533) =.? (x2_1536)) && ((
                        y1_1534) =.? ((nat_mod_zero ) -% (
                          y2_1537))))):bool then (g1add_a (p_1531) (
                    q_1532)) else ((nat_mod_zero , nat_mod_zero , true))))))))).

Definition g1mul (m_1539 : scalar_t) (p_1540 : g1_t) : g1_t :=
  let t_1541 : (fp_t × fp_t × bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_1541 :=
    foldi (usize 0) (usize 256) (fun i_1542 t_1541 =>
      let t_1541 :=
        g1double (t_1541) in 
      let '(t_1541) :=
        if nat_mod_bit (m_1539) ((usize 255) - (i_1542)):bool then (
          let t_1541 :=
            g1add (t_1541) (p_1540) in 
          (t_1541)) else ((t_1541)) in 
      (t_1541))
    t_1541 in 
  t_1541.

Definition g1neg (p_1543 : g1_t) : g1_t :=
  let '(x_1544, y_1545, inf_1546) :=
    p_1543 in 
  (x_1544, (nat_mod_zero ) -% (y_1545), inf_1546).

Definition g2add_a (p_1547 : g2_t) (q_1548 : g2_t) : g2_t :=
  let '(x1_1549, y1_1550, _) :=
    p_1547 in 
  let '(x2_1551, y2_1552, _) :=
    q_1548 in 
  let x_diff_1553 : (fp_t × fp_t) :=
    fp2sub (x2_1551) (x1_1549) in 
  let y_diff_1554 : (fp_t × fp_t) :=
    fp2sub (y2_1552) (y1_1550) in 
  let xovery_1555 : (fp_t × fp_t) :=
    fp2mul (y_diff_1554) (fp2inv (x_diff_1553)) in 
  let t1_1556 : (fp_t × fp_t) :=
    fp2mul (xovery_1555) (xovery_1555) in 
  let t2_1557 : (fp_t × fp_t) :=
    fp2sub (t1_1556) (x1_1549) in 
  let x3_1558 : (fp_t × fp_t) :=
    fp2sub (t2_1557) (x2_1551) in 
  let t1_1559 : (fp_t × fp_t) :=
    fp2sub (x1_1549) (x3_1558) in 
  let t2_1560 : (fp_t × fp_t) :=
    fp2mul (xovery_1555) (t1_1559) in 
  let y3_1561 : (fp_t × fp_t) :=
    fp2sub (t2_1560) (y1_1550) in 
  (x3_1558, y3_1561, false).

Definition g2double_a (p_1562 : g2_t) : g2_t :=
  let '(x1_1563, y1_1564, _) :=
    p_1562 in 
  let x12_1565 : (fp_t × fp_t) :=
    fp2mul (x1_1563) (x1_1563) in 
  let t1_1566 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_1565) in 
  let t2_1567 : (fp_t × fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_1564)) in 
  let xovery_1568 : (fp_t × fp_t) :=
    fp2mul (t1_1566) (t2_1567) in 
  let t1_1569 : (fp_t × fp_t) :=
    fp2mul (xovery_1568) (xovery_1568) in 
  let t2_1570 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_1563) in 
  let x3_1571 : (fp_t × fp_t) :=
    fp2sub (t1_1569) (t2_1570) in 
  let t1_1572 : (fp_t × fp_t) :=
    fp2sub (x1_1563) (x3_1571) in 
  let t2_1573 : (fp_t × fp_t) :=
    fp2mul (xovery_1568) (t1_1572) in 
  let y3_1574 : (fp_t × fp_t) :=
    fp2sub (t2_1573) (y1_1564) in 
  (x3_1571, y3_1574, false).

Definition g2double (p_1575 : g2_t) : g2_t :=
  let '(x1_1576, y1_1577, inf1_1578) :=
    p_1575 in 
  (if (((y1_1577) !=.? (fp2zero )) && (negb (inf1_1578))):bool then (
      g2double_a (p_1575)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_1579 : g2_t) (q_1580 : g2_t) : g2_t :=
  let '(x1_1581, y1_1582, inf1_1583) :=
    p_1579 in 
  let '(x2_1584, y2_1585, inf2_1586) :=
    q_1580 in 
  (if (inf1_1583):bool then (q_1580) else ((if (inf2_1586):bool then (
          p_1579) else ((if ((p_1579) =.? (q_1580)):bool then (g2double (
                p_1579)) else ((if (negb (((x1_1581) =.? (x2_1584)) && ((
                        y1_1582) =.? (fp2neg (y2_1585))))):bool then (g2add_a (
                    p_1579) (q_1580)) else ((fp2zero , fp2zero , true))))))))).

Definition g2mul (m_1587 : scalar_t) (p_1588 : g2_t) : g2_t :=
  let t_1589 : (fp2_t × fp2_t × bool) :=
    (fp2zero , fp2zero , true) in 
  let t_1589 :=
    foldi (usize 0) (usize 256) (fun i_1590 t_1589 =>
      let t_1589 :=
        g2double (t_1589) in 
      let '(t_1589) :=
        if nat_mod_bit (m_1587) ((usize 255) - (i_1590)):bool then (
          let t_1589 :=
            g2add (t_1589) (p_1588) in 
          (t_1589)) else ((t_1589)) in 
      (t_1589))
    t_1589 in 
  t_1589.

Definition g2neg (p_1591 : g2_t) : g2_t :=
  let '(x_1592, y_1593, inf_1594) :=
    p_1591 in 
  (x_1592, fp2neg (y_1593), inf_1594).

Definition twist (p_1595 : g1_t) : (fp12_t × fp12_t) :=
  let '(p0_1596, p1_1597, _) :=
    p_1595 in 
  let x_1598 : ((fp2_t × fp2_t × fp2_t) × fp6_t) :=
    ((fp2zero , fp2fromfp (p0_1596), fp2zero ), fp6zero ) in 
  let y_1599 : (fp6_t × (fp2_t × fp2_t × fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_1597), fp2zero )) in 
  (x_1598, y_1599).

Definition line_double_p (r_1600 : g2_t) (p_1601 : g1_t) : fp12_t :=
  let '(r0_1602, r1_1603, _) :=
    r_1600 in 
  let a_1604 : (fp_t × fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_1602) (r0_1602)) in 
  let a_1605 : (fp_t × fp_t) :=
    fp2mul (a_1604) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_1603))) in 
  let b_1606 : (fp_t × fp_t) :=
    fp2sub (r1_1603) (fp2mul (a_1605) (r0_1602)) in 
  let a_1607 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1605)) in 
  let b_1608 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1606)) in 
  let '(x_1609, y_1610) :=
    twist (p_1601) in 
  fp12neg (fp12sub (fp12sub (y_1610) (fp12mul (a_1607) (x_1609))) (b_1608)).

Definition line_add_p
  (r_1611 : g2_t)
  (q_1612 : g2_t)
  (p_1613 : g1_t)
  : fp12_t :=
  let '(r0_1614, r1_1615, _) :=
    r_1611 in 
  let '(q0_1616, q1_1617, _) :=
    q_1612 in 
  let a_1618 : (fp_t × fp_t) :=
    fp2mul (fp2sub (q1_1617) (r1_1615)) (fp2inv (fp2sub (q0_1616) (
          r0_1614))) in 
  let b_1619 : (fp_t × fp_t) :=
    fp2sub (r1_1615) (fp2mul (a_1618) (r0_1614)) in 
  let a_1620 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1618)) in 
  let b_1621 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1619)) in 
  let '(x_1622, y_1623) :=
    twist (p_1613) in 
  fp12neg (fp12sub (fp12sub (y_1623) (fp12mul (a_1620) (x_1622))) (b_1621)).

Definition frobenius (f_1624 : fp12_t) : fp12_t :=
  let '((g0_1625, g1_1626, g2_1627), (h0_1628, h1_1629, h2_1630)) :=
    f_1624 in 
  let t1_1631 : (fp_t × fp_t) :=
    fp2conjugate (g0_1625) in 
  let t2_1632 : (fp_t × fp_t) :=
    fp2conjugate (h0_1628) in 
  let t3_1633 : (fp_t × fp_t) :=
    fp2conjugate (g1_1626) in 
  let t4_1634 : (fp_t × fp_t) :=
    fp2conjugate (h1_1629) in 
  let t5_1635 : (fp_t × fp_t) :=
    fp2conjugate (g2_1627) in 
  let t6_1636 : (fp_t × fp_t) :=
    fp2conjugate (h2_1630) in 
  let c1_1637 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_1638 : seq uint8 :=
    array_to_le_bytes (c1_1637) in 
  let c1_1639 : fp_t :=
    nat_mod_from_byte_seq_le (c1_1638) : fp_t in 
  let c2_1640 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_1641 : seq uint8 :=
    array_to_le_bytes (c2_1640) in 
  let c2_1642 : fp_t :=
    nat_mod_from_byte_seq_le (c2_1641) : fp_t in 
  let gamma11_1643 : (fp_t × fp_t) :=
    (c1_1639, c2_1642) in 
  let gamma12_1644 : (fp_t × fp_t) :=
    fp2mul (gamma11_1643) (gamma11_1643) in 
  let gamma13_1645 : (fp_t × fp_t) :=
    fp2mul (gamma12_1644) (gamma11_1643) in 
  let gamma14_1646 : (fp_t × fp_t) :=
    fp2mul (gamma13_1645) (gamma11_1643) in 
  let gamma15_1647 : (fp_t × fp_t) :=
    fp2mul (gamma14_1646) (gamma11_1643) in 
  let t2_1648 : (fp_t × fp_t) :=
    fp2mul (t2_1632) (gamma11_1643) in 
  let t3_1649 : (fp_t × fp_t) :=
    fp2mul (t3_1633) (gamma12_1644) in 
  let t4_1650 : (fp_t × fp_t) :=
    fp2mul (t4_1634) (gamma13_1645) in 
  let t5_1651 : (fp_t × fp_t) :=
    fp2mul (t5_1635) (gamma14_1646) in 
  let t6_1652 : (fp_t × fp_t) :=
    fp2mul (t6_1636) (gamma15_1647) in 
  ((t1_1631, t3_1649, t5_1651), (t2_1648, t4_1650, t6_1652)).

Definition final_exponentiation (f_1653 : fp12_t) : fp12_t :=
  let fp6_1654 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1653) in 
  let finv_1655 : (fp6_t × fp6_t) :=
    fp12inv (f_1653) in 
  let fp6_1_1656 : (fp6_t × fp6_t) :=
    fp12mul (fp6_1654) (finv_1655) in 
  let fp8_1657 : (fp6_t × fp6_t) :=
    frobenius (frobenius (fp6_1_1656)) in 
  let f_1658 : (fp6_t × fp6_t) :=
    fp12mul (fp8_1657) (fp6_1_1656) in 
  let u_1659 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let u_half_1660 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 7566188111470821376) : scalar_t in 
  let t0_1661 : (fp6_t × fp6_t) :=
    fp12mul (f_1658) (f_1658) in 
  let t1_1662 : (fp6_t × fp6_t) :=
    fp12exp (t0_1661) (u_1659) in 
  let t1_1663 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1662) in 
  let t2_1664 : (fp6_t × fp6_t) :=
    fp12exp (t1_1663) (u_half_1660) in 
  let t2_1665 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1664) in 
  let t3_1666 : (fp6_t × fp6_t) :=
    fp12conjugate (f_1658) in 
  let t1_1667 : (fp6_t × fp6_t) :=
    fp12mul (t3_1666) (t1_1663) in 
  let t1_1668 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1667) in 
  let t1_1669 : (fp6_t × fp6_t) :=
    fp12mul (t1_1668) (t2_1665) in 
  let t2_1670 : (fp6_t × fp6_t) :=
    fp12exp (t1_1669) (u_1659) in 
  let t2_1671 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1670) in 
  let t3_1672 : (fp6_t × fp6_t) :=
    fp12exp (t2_1671) (u_1659) in 
  let t3_1673 : (fp6_t × fp6_t) :=
    fp12conjugate (t3_1672) in 
  let t1_1674 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1669) in 
  let t3_1675 : (fp6_t × fp6_t) :=
    fp12mul (t1_1674) (t3_1673) in 
  let t1_1676 : (fp6_t × fp6_t) :=
    fp12conjugate (t1_1674) in 
  let t1_1677 : (fp6_t × fp6_t) :=
    frobenius (frobenius (frobenius (t1_1676))) in 
  let t2_1678 : (fp6_t × fp6_t) :=
    frobenius (frobenius (t2_1671)) in 
  let t1_1679 : (fp6_t × fp6_t) :=
    fp12mul (t1_1677) (t2_1678) in 
  let t2_1680 : (fp6_t × fp6_t) :=
    fp12exp (t3_1675) (u_1659) in 
  let t2_1681 : (fp6_t × fp6_t) :=
    fp12conjugate (t2_1680) in 
  let t2_1682 : (fp6_t × fp6_t) :=
    fp12mul (t2_1681) (t0_1661) in 
  let t2_1683 : (fp6_t × fp6_t) :=
    fp12mul (t2_1682) (f_1658) in 
  let t1_1684 : (fp6_t × fp6_t) :=
    fp12mul (t1_1679) (t2_1683) in 
  let t2_1685 : (fp6_t × fp6_t) :=
    frobenius (t3_1675) in 
  let t1_1686 : (fp6_t × fp6_t) :=
    fp12mul (t1_1684) (t2_1685) in 
  t1_1686.

Definition pairing (p_1687 : g1_t) (q_1688 : g2_t) : fp12_t :=
  let t_1689 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_1690 : (fp2_t × fp2_t × bool) :=
    q_1688 in 
  let f_1691 : (fp6_t × fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_1690, f_1691) :=
    foldi (usize 1) (usize 64) (fun i_1692 '(r_1690, f_1691) =>
      let lrr_1693 : (fp6_t × fp6_t) :=
        line_double_p (r_1690) (p_1687) in 
      let r_1690 :=
        g2double (r_1690) in 
      let f_1691 :=
        fp12mul (fp12mul (f_1691) (f_1691)) (lrr_1693) in 
      let '(r_1690, f_1691) :=
        if nat_mod_bit (t_1689) (((usize 64) - (i_1692)) - (
            usize 1)):bool then (let lrq_1694 : (fp6_t × fp6_t) :=
            line_add_p (r_1690) (q_1688) (p_1687) in 
          let r_1690 :=
            g2add (r_1690) (q_1688) in 
          let f_1691 :=
            fp12mul (f_1691) (lrq_1694) in 
          (r_1690, f_1691)) else ((r_1690, f_1691)) in 
      (r_1690, f_1691))
    (r_1690, f_1691) in 
  final_exponentiation (fp12conjugate (f_1691)).

Definition test_fp2_prop_add_neg (a_1695 : fp2_t) : bool :=
  let b_1696 : (fp_t × fp_t) :=
    fp2neg (a_1695) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_1695) (b_1696)).
(*QuickChick (
  forAll g_fp2_t (fun a_1695 : fp2_t =>test_fp2_prop_add_neg a_1695)).*)


Definition test_fp2_prop_mul_inv (a_1697 : fp2_t) : bool :=
  let b_1698 : (fp_t × fp_t) :=
    fp2inv (a_1697) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_1697) (b_1698)).
(*QuickChick (
  forAll g_fp2_t (fun a_1697 : fp2_t =>test_fp2_prop_mul_inv a_1697)).*)


Definition test_extraction_issue  : bool :=
  let b_1699 : (fp_t × fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_1699)).
(*QuickChick (test_extraction_issue).*)


Definition test_fp6_prop_mul_inv (a_1700 : fp6_t) : bool :=
  let b_1701 : (fp2_t × fp2_t × fp2_t) :=
    fp6inv (a_1700) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_1700) (b_1701)).
(*QuickChick (
  forAll g_fp6_t (fun a_1700 : fp6_t =>test_fp6_prop_mul_inv a_1700)).*)


Definition test_fp6_prop_add_neg (a_1702 : fp6_t) : bool :=
  let b_1703 : (fp2_t × fp2_t × fp2_t) :=
    fp6neg (a_1702) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_1702) (b_1703)).
(*QuickChick (
  forAll g_fp6_t (fun a_1702 : fp6_t =>test_fp6_prop_add_neg a_1702)).*)


Definition test_fp12_prop_add_neg (a_1704 : fp12_t) : bool :=
  let b_1705 : (fp6_t × fp6_t) :=
    fp12neg (a_1704) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_1704) (
      b_1705)).
(*QuickChick (
  forAll g_fp12_t (fun a_1704 : fp12_t =>test_fp12_prop_add_neg a_1704)).*)


Definition test_fp12_prop_mul_inv (a_1706 : fp12_t) : bool :=
  let b_1707 : (fp6_t × fp6_t) :=
    fp12inv (a_1706) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_1706) (
      b_1707)).
(*QuickChick (
  forAll g_fp12_t (fun a_1706 : fp12_t =>test_fp12_prop_mul_inv a_1706)).*)


