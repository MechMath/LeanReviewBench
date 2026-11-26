import Batteries.Data.Array.Lemmas
import Lean
import Lean.Elab.Declaration
import Lean.Elab.Exception
import Lean.Environment
import Lean.Meta.Basic
import Lean.ToExpr
import Lean.Util
import Lean.Util.CollectAxioms
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Cases
import dep.equational_theories.EndToEnd.Basic
import dep.equational_theories.EndToEnd.Certificate
import dep.equational_theories.EndToEnd.Dual
import dep.equational_theories.EndToEnd.Load
import dep.equational_theories.EquationLawConversion
import dep.equational_theories.Equations.Basic
import dep.equational_theories.Equations.Command
import dep.equational_theories.Equations.Eqns1000_1999
import dep.equational_theories.Equations.Eqns1_999
import dep.equational_theories.Equations.Eqns2000_2999
import dep.equational_theories.Equations.Eqns3000_3999
import dep.equational_theories.Equations.Eqns4000_4694
import dep.equational_theories.Equations.LawsComplete
import dep.equational_theories.FreeMagma
import dep.equational_theories.Homomorphisms
import dep.equational_theories.Magma
import dep.equational_theories.MagmaLaw
import dep.equational_theories.MagmaOp
import dep.equational_theories.ParseImplications
import dep.equational_theories.Preorder
import dep.equational_theories.RArray

namespace EndToEnd

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
def _root_.EndToEnd.dualtable1 : RArray EndToEnd.DualFact :=
RArray.branch 1000
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2000, dual := 1797, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2001, dual := 1732, proof := sorry })
                      (RArray.leaf { law := 2002, dual := 1799, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2003, dual := 1674, proof := sorry })
                      (RArray.leaf { law := 2004, dual := 1821, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2005, dual := 1778, proof := sorry })
                      (RArray.leaf { law := 2006, dual := 1748, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2007, dual := 1824, proof := sorry })
                      (RArray.leaf { law := 2008, dual := 1642, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2009, dual := 1713, proof := sorry })
                      (RArray.leaf { law := 2010, dual := 1707, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2011, dual := 1699, proof := sorry })
                      (RArray.leaf { law := 2012, dual := 1716, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2013, dual := 1676, proof := sorry })
                      (RArray.leaf { law := 2014, dual := 1750, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2015, dual := 1812, proof := sorry })
                      (RArray.leaf { law := 2016, dual := 1785, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2017, dual := 1827, proof := sorry })
                      (RArray.leaf { law := 2018, dual := 1670, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2019, dual := 1816, proof := sorry })
                      (RArray.leaf { law := 2020, dual := 1744, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2021, dual := 1782, proof := sorry })
                      (RArray.leaf { law := 2022, dual := 1819, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2023, dual := 1662, proof := sorry })
                      (RArray.leaf { law := 2024, dual := 1801, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2025, dual := 1795, proof := sorry })
                      (RArray.leaf { law := 2026, dual := 1736, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2027, dual := 1804, proof := sorry })
                      (RArray.leaf { law := 2028, dual := 1679, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2029, dual := 1826, proof := sorry })
                      (RArray.leaf { law := 2030, dual := 1814, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2031, dual := 1787, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2032, dual := 1753, proof := sorry })
                      (RArray.leaf { law := 2033, dual := 1830, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2034, dual := 1425, proof := sorry })
                      (RArray.leaf { law := 2035, dual := 1477, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2036, dual := 1440, proof := sorry })
                      (RArray.leaf { law := 2037, dual := 1514, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2038, dual := 1551, proof := sorry })
                      (RArray.leaf { law := 2039, dual := 1430, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2040, dual := 1487, proof := sorry })
                      (RArray.leaf { law := 2041, dual := 1497, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2042, dual := 1450, proof := sorry })
                      (RArray.leaf { law := 2043, dual := 1524, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2044, dual := 1585, proof := sorry })
                      (RArray.leaf { law := 2045, dual := 1460, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2046, dual := 1568, proof := sorry })
                      (RArray.leaf { law := 2047, dual := 1534, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2048, dual := 1602, proof := sorry })
                      (RArray.leaf { law := 2049, dual := 1427, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2050, dual := 1480, proof := sorry })
                      (RArray.leaf { law := 2051, dual := 1483, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2052, dual := 1443, proof := sorry })
                      (RArray.leaf { law := 2053, dual := 1517, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2054, dual := 1559, proof := sorry })
                      (RArray.leaf { law := 2055, dual := 1446, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2056, dual := 1555, proof := sorry })
                      (RArray.leaf { law := 2057, dual := 1520, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2058, dual := 1563, proof := sorry })
                      (RArray.leaf { law := 2059, dual := 1433, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2060, dual := 1490, proof := sorry })
                      (RArray.leaf { law := 2061, dual := 1505, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2062, dual := 1453, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2063, dual := 1527, proof := sorry })
                      (RArray.leaf { law := 2064, dual := 1593, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2065, dual := 1468, proof := sorry })
                      (RArray.leaf { law := 2066, dual := 1572, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2067, dual := 1542, proof := sorry })
                      (RArray.leaf { law := 2068, dual := 1617, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2069, dual := 1436, proof := sorry })
                      (RArray.leaf { law := 2070, dual := 1501, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2071, dual := 1493, proof := sorry })
                      (RArray.leaf { law := 2072, dual := 1509, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2073, dual := 1464, proof := sorry })
                      (RArray.leaf { law := 2074, dual := 1538, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2075, dual := 1576, proof := sorry })
                      (RArray.leaf { law := 2076, dual := 1612, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2077, dual := 1456, proof := sorry })
                      (RArray.leaf { law := 2078, dual := 1589, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2079, dual := 1530, proof := sorry })
                      (RArray.leaf { law := 2080, dual := 1597, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2081, dual := 1472, proof := sorry })
                      (RArray.leaf { law := 2082, dual := 1607, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2083, dual := 1580, proof := sorry })
                      (RArray.leaf { law := 2084, dual := 1546, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2085, dual := 1622, proof := sorry })
                      (RArray.leaf { law := 2086, dual := 1426, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2087, dual := 1478, proof := sorry })
                      (RArray.leaf { law := 2088, dual := 1479, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2089, dual := 1441, proof := sorry })
                      (RArray.leaf { law := 2090, dual := 1515, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2091, dual := 1553, proof := sorry })
                      (RArray.leaf { law := 2092, dual := 1442, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2093, dual := 1552, proof := sorry })
                      (RArray.leaf { law := 2094, dual := 1516, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2095, dual := 1554, proof := sorry })
                      (RArray.leaf { law := 2096, dual := 1431, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2097, dual := 1488, proof := sorry })
                      (RArray.leaf { law := 2098, dual := 1499, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2099, dual := 1451, proof := sorry })
                      (RArray.leaf { law := 2100, dual := 1525, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2101, dual := 1587, proof := sorry })
                      (RArray.leaf { law := 2102, dual := 1462, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2103, dual := 1569, proof := sorry })
                      (RArray.leaf { law := 2104, dual := 1536, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2105, dual := 1605, proof := sorry })
                      (RArray.leaf { law := 2106, dual := 1432, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2107, dual := 1498, proof := sorry })
                      (RArray.leaf { law := 2108, dual := 1489, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2109, dual := 1500, proof := sorry })
                      (RArray.leaf { law := 2110, dual := 1461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2111, dual := 1535, proof := sorry })
                      (RArray.leaf { law := 2112, dual := 1570, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2113, dual := 1604, proof := sorry })
                      (RArray.leaf { law := 2114, dual := 1452, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2115, dual := 1586, proof := sorry })
                      (RArray.leaf { law := 2116, dual := 1526, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2117, dual := 1588, proof := sorry })
                      (RArray.leaf { law := 2118, dual := 1463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2119, dual := 1603, proof := sorry })
                      (RArray.leaf { law := 2120, dual := 1571, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2121, dual := 1537, proof := sorry })
                      (RArray.leaf { law := 2122, dual := 1606, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2123, dual := 1428, proof := sorry })
                      (RArray.leaf { law := 2124, dual := 1481, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2125, dual := 1485, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2126, dual := 1444, proof := sorry })
                      (RArray.leaf { law := 2127, dual := 1518, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2128, dual := 1561, proof := sorry })
                      (RArray.leaf { law := 2129, dual := 1448, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2130, dual := 1556, proof := sorry })
                      (RArray.leaf { law := 2131, dual := 1522, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2132, dual := 1566, proof := sorry })
                      (RArray.leaf { law := 2133, dual := 1434, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2134, dual := 1491, proof := sorry })
                      (RArray.leaf { law := 2135, dual := 1507, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2136, dual := 1454, proof := sorry })
                      (RArray.leaf { law := 2137, dual := 1528, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2138, dual := 1595, proof := sorry })
                      (RArray.leaf { law := 2139, dual := 1470, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2140, dual := 1573, proof := sorry })
                      (RArray.leaf { law := 2141, dual := 1544, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2142, dual := 1620, proof := sorry })
                      (RArray.leaf { law := 2143, dual := 1438, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2144, dual := 1502, proof := sorry })
                      (RArray.leaf { law := 2145, dual := 1495, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2146, dual := 1512, proof := sorry })
                      (RArray.leaf { law := 2147, dual := 1465, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2148, dual := 1539, proof := sorry })
                      (RArray.leaf { law := 2149, dual := 1578, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2150, dual := 1614, proof := sorry })
                      (RArray.leaf { law := 2151, dual := 1458, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2152, dual := 1590, proof := sorry })
                      (RArray.leaf { law := 2153, dual := 1532, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2154, dual := 1600, proof := sorry })
                      (RArray.leaf { law := 2155, dual := 1475, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2156, dual := 1608, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2157, dual := 1583, proof := sorry })
                      (RArray.leaf { law := 2158, dual := 1549, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2159, dual := 1626, proof := sorry })
                      (RArray.leaf { law := 2160, dual := 1429, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2161, dual := 1484, proof := sorry })
                      (RArray.leaf { law := 2162, dual := 1482, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2163, dual := 1486, proof := sorry })
                      (RArray.leaf { law := 2164, dual := 1447, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2165, dual := 1521, proof := sorry })
                      (RArray.leaf { law := 2166, dual := 1557, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2167, dual := 1565, proof := sorry })
                      (RArray.leaf { law := 2168, dual := 1445, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2169, dual := 1560, proof := sorry })
                      (RArray.leaf { law := 2170, dual := 1519, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2171, dual := 1562, proof := sorry })
                      (RArray.leaf { law := 2172, dual := 1449, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2173, dual := 1564, proof := sorry })
                      (RArray.leaf { law := 2174, dual := 1558, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2175, dual := 1523, proof := sorry })
                      (RArray.leaf { law := 2176, dual := 1567, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2177, dual := 1437, proof := sorry })
                      (RArray.leaf { law := 2178, dual := 1494, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2179, dual := 1503, proof := sorry })
                      (RArray.leaf { law := 2180, dual := 1511, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2181, dual := 1457, proof := sorry })
                      (RArray.leaf { law := 2182, dual := 1531, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2183, dual := 1591, proof := sorry })
                      (RArray.leaf { law := 2184, dual := 1599, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2185, dual := 1466, proof := sorry })
                      (RArray.leaf { law := 2186, dual := 1577, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2187, dual := 1540, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2188, dual := 1615, proof := sorry })
                      (RArray.leaf { law := 2189, dual := 1474, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2190, dual := 1581, proof := sorry })
                      (RArray.leaf { law := 2191, dual := 1610, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2192, dual := 1548, proof := sorry })
                      (RArray.leaf { law := 2193, dual := 1625, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2194, dual := 1435, proof := sorry })
                      (RArray.leaf { law := 2195, dual := 1506, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2196, dual := 1492, proof := sorry })
                      (RArray.leaf { law := 2197, dual := 1508, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2198, dual := 1469, proof := sorry })
                      (RArray.leaf { law := 2199, dual := 1543, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2200, dual := 1574, proof := sorry })
                      (RArray.leaf { law := 2201, dual := 1619, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2202, dual := 1455, proof := sorry })
                      (RArray.leaf { law := 2203, dual := 1594, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2204, dual := 1529, proof := sorry })
                      (RArray.leaf { law := 2205, dual := 1596, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2206, dual := 1471, proof := sorry })
                      (RArray.leaf { law := 2207, dual := 1618, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2208, dual := 1575, proof := sorry })
                      (RArray.leaf { law := 2209, dual := 1545, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2210, dual := 1621, proof := sorry })
                      (RArray.leaf { law := 2211, dual := 1439, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2212, dual := 1510, proof := sorry })
                      (RArray.leaf { law := 2213, dual := 1504, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2214, dual := 1496, proof := sorry })
                      (RArray.leaf { law := 2215, dual := 1513, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2216, dual := 1473, proof := sorry })
                      (RArray.leaf { law := 2217, dual := 1547, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2218, dual := 1609, proof := sorry })
                      (RArray.leaf { law := 2219, dual := 1582, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2220, dual := 1624, proof := sorry })
                      (RArray.leaf { law := 2221, dual := 1467, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2222, dual := 1613, proof := sorry })
                      (RArray.leaf { law := 2223, dual := 1541, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2224, dual := 1579, proof := sorry })
                      (RArray.leaf { law := 2225, dual := 1616, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2226, dual := 1459, proof := sorry })
                      (RArray.leaf { law := 2227, dual := 1598, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2228, dual := 1592, proof := sorry })
                      (RArray.leaf { law := 2229, dual := 1533, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2230, dual := 1601, proof := sorry })
                      (RArray.leaf { law := 2231, dual := 1476, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2232, dual := 1623, proof := sorry })
                      (RArray.leaf { law := 2233, dual := 1611, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2234, dual := 1584, proof := sorry })
                      (RArray.leaf { law := 2235, dual := 1550, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2236, dual := 1627, proof := sorry })
                      (RArray.leaf { law := 2237, dual := 1222, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2238, dual := 1274, proof := sorry })
                      (RArray.leaf { law := 2239, dual := 1237, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2240, dual := 1311, proof := sorry })
                      (RArray.leaf { law := 2241, dual := 1348, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2242, dual := 1227, proof := sorry })
                      (RArray.leaf { law := 2243, dual := 1284, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2244, dual := 1294, proof := sorry })
                      (RArray.leaf { law := 2245, dual := 1247, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2246, dual := 1321, proof := sorry })
                      (RArray.leaf { law := 2247, dual := 1382, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2248, dual := 1257, proof := sorry })
                      (RArray.leaf { law := 2249, dual := 1365, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2250, dual := 1331, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2251, dual := 1399, proof := sorry })
                      (RArray.leaf { law := 2252, dual := 1224, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2253, dual := 1277, proof := sorry })
                      (RArray.leaf { law := 2254, dual := 1280, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2255, dual := 1240, proof := sorry })
                      (RArray.leaf { law := 2256, dual := 1314, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2257, dual := 1356, proof := sorry })
                      (RArray.leaf { law := 2258, dual := 1243, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2259, dual := 1352, proof := sorry })
                      (RArray.leaf { law := 2260, dual := 1317, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2261, dual := 1360, proof := sorry })
                      (RArray.leaf { law := 2262, dual := 1230, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2263, dual := 1287, proof := sorry })
                      (RArray.leaf { law := 2264, dual := 1302, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2265, dual := 1250, proof := sorry })
                      (RArray.leaf { law := 2266, dual := 1324, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2267, dual := 1390, proof := sorry })
                      (RArray.leaf { law := 2268, dual := 1265, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2269, dual := 1369, proof := sorry })
                      (RArray.leaf { law := 2270, dual := 1339, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2271, dual := 1414, proof := sorry })
                      (RArray.leaf { law := 2272, dual := 1233, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2273, dual := 1298, proof := sorry })
                      (RArray.leaf { law := 2274, dual := 1290, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2275, dual := 1306, proof := sorry })
                      (RArray.leaf { law := 2276, dual := 1261, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2277, dual := 1335, proof := sorry })
                      (RArray.leaf { law := 2278, dual := 1373, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2279, dual := 1409, proof := sorry })
                      (RArray.leaf { law := 2280, dual := 1253, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2281, dual := 1386, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2282, dual := 1327, proof := sorry })
                      (RArray.leaf { law := 2283, dual := 1394, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2284, dual := 1269, proof := sorry })
                      (RArray.leaf { law := 2285, dual := 1404, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2286, dual := 1377, proof := sorry })
                      (RArray.leaf { law := 2287, dual := 1343, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2288, dual := 1419, proof := sorry })
                      (RArray.leaf { law := 2289, dual := 1223, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2290, dual := 1275, proof := sorry })
                      (RArray.leaf { law := 2291, dual := 1276, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2292, dual := 1238, proof := sorry })
                      (RArray.leaf { law := 2293, dual := 1312, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2294, dual := 1350, proof := sorry })
                      (RArray.leaf { law := 2295, dual := 1239, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2296, dual := 1349, proof := sorry })
                      (RArray.leaf { law := 2297, dual := 1313, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2298, dual := 1351, proof := sorry })
                      (RArray.leaf { law := 2299, dual := 1228, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2300, dual := 1285, proof := sorry })
                      (RArray.leaf { law := 2301, dual := 1296, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2302, dual := 1248, proof := sorry })
                      (RArray.leaf { law := 2303, dual := 1322, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2304, dual := 1384, proof := sorry })
                      (RArray.leaf { law := 2305, dual := 1259, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2306, dual := 1366, proof := sorry })
                      (RArray.leaf { law := 2307, dual := 1333, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2308, dual := 1402, proof := sorry })
                      (RArray.leaf { law := 2309, dual := 1229, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2310, dual := 1295, proof := sorry })
                      (RArray.leaf { law := 2311, dual := 1286, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2312, dual := 1297, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2313, dual := 1258, proof := sorry })
                      (RArray.leaf { law := 2314, dual := 1332, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2315, dual := 1367, proof := sorry })
                      (RArray.leaf { law := 2316, dual := 1401, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2317, dual := 1249, proof := sorry })
                      (RArray.leaf { law := 2318, dual := 1383, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2319, dual := 1323, proof := sorry })
                      (RArray.leaf { law := 2320, dual := 1385, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2321, dual := 1260, proof := sorry })
                      (RArray.leaf { law := 2322, dual := 1400, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2323, dual := 1368, proof := sorry })
                      (RArray.leaf { law := 2324, dual := 1334, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2325, dual := 1403, proof := sorry })
                      (RArray.leaf { law := 2326, dual := 1225, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2327, dual := 1278, proof := sorry })
                      (RArray.leaf { law := 2328, dual := 1282, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2329, dual := 1241, proof := sorry })
                      (RArray.leaf { law := 2330, dual := 1315, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2331, dual := 1358, proof := sorry })
                      (RArray.leaf { law := 2332, dual := 1245, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2333, dual := 1353, proof := sorry })
                      (RArray.leaf { law := 2334, dual := 1319, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2335, dual := 1363, proof := sorry })
                      (RArray.leaf { law := 2336, dual := 1231, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2337, dual := 1288, proof := sorry })
                      (RArray.leaf { law := 2338, dual := 1304, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2339, dual := 1251, proof := sorry })
                      (RArray.leaf { law := 2340, dual := 1325, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2341, dual := 1392, proof := sorry })
                      (RArray.leaf { law := 2342, dual := 1267, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2343, dual := 1370, proof := sorry })
                      (RArray.leaf { law := 2344, dual := 1341, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2345, dual := 1417, proof := sorry })
                      (RArray.leaf { law := 2346, dual := 1235, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2347, dual := 1299, proof := sorry })
                      (RArray.leaf { law := 2348, dual := 1292, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2349, dual := 1309, proof := sorry })
                      (RArray.leaf { law := 2350, dual := 1262, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2351, dual := 1336, proof := sorry })
                      (RArray.leaf { law := 2352, dual := 1375, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2353, dual := 1411, proof := sorry })
                      (RArray.leaf { law := 2354, dual := 1255, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2355, dual := 1387, proof := sorry })
                      (RArray.leaf { law := 2356, dual := 1329, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2357, dual := 1397, proof := sorry })
                      (RArray.leaf { law := 2358, dual := 1272, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2359, dual := 1405, proof := sorry })
                      (RArray.leaf { law := 2360, dual := 1380, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2361, dual := 1346, proof := sorry })
                      (RArray.leaf { law := 2362, dual := 1423, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2363, dual := 1226, proof := sorry })
                      (RArray.leaf { law := 2364, dual := 1281, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2365, dual := 1279, proof := sorry })
                      (RArray.leaf { law := 2366, dual := 1283, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2367, dual := 1244, proof := sorry })
                      (RArray.leaf { law := 2368, dual := 1318, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2369, dual := 1354, proof := sorry })
                      (RArray.leaf { law := 2370, dual := 1362, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2371, dual := 1242, proof := sorry })
                      (RArray.leaf { law := 2372, dual := 1357, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2373, dual := 1316, proof := sorry })
                      (RArray.leaf { law := 2374, dual := 1359, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2375, dual := 1246, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2376, dual := 1361, proof := sorry })
                      (RArray.leaf { law := 2377, dual := 1355, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2378, dual := 1320, proof := sorry })
                      (RArray.leaf { law := 2379, dual := 1364, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2380, dual := 1234, proof := sorry })
                      (RArray.leaf { law := 2381, dual := 1291, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2382, dual := 1300, proof := sorry })
                      (RArray.leaf { law := 2383, dual := 1308, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2384, dual := 1254, proof := sorry })
                      (RArray.leaf { law := 2385, dual := 1328, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2386, dual := 1388, proof := sorry })
                      (RArray.leaf { law := 2387, dual := 1396, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2388, dual := 1263, proof := sorry })
                      (RArray.leaf { law := 2389, dual := 1374, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2390, dual := 1337, proof := sorry })
                      (RArray.leaf { law := 2391, dual := 1412, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2392, dual := 1271, proof := sorry })
                      (RArray.leaf { law := 2393, dual := 1378, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2394, dual := 1407, proof := sorry })
                      (RArray.leaf { law := 2395, dual := 1345, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2396, dual := 1422, proof := sorry })
                      (RArray.leaf { law := 2397, dual := 1232, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2398, dual := 1303, proof := sorry })
                      (RArray.leaf { law := 2399, dual := 1289, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2400, dual := 1305, proof := sorry })
                      (RArray.leaf { law := 2401, dual := 1266, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2402, dual := 1340, proof := sorry })
                      (RArray.leaf { law := 2403, dual := 1371, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2404, dual := 1416, proof := sorry })
                      (RArray.leaf { law := 2405, dual := 1252, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2406, dual := 1391, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2407, dual := 1326, proof := sorry })
                      (RArray.leaf { law := 2408, dual := 1393, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2409, dual := 1268, proof := sorry })
                      (RArray.leaf { law := 2410, dual := 1415, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2411, dual := 1372, proof := sorry })
                      (RArray.leaf { law := 2412, dual := 1342, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2413, dual := 1418, proof := sorry })
                      (RArray.leaf { law := 2414, dual := 1236, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2415, dual := 1307, proof := sorry })
                      (RArray.leaf { law := 2416, dual := 1301, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2417, dual := 1293, proof := sorry })
                      (RArray.leaf { law := 2418, dual := 1310, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2419, dual := 1270, proof := sorry })
                      (RArray.leaf { law := 2420, dual := 1344, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2421, dual := 1406, proof := sorry })
                      (RArray.leaf { law := 2422, dual := 1379, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2423, dual := 1421, proof := sorry })
                      (RArray.leaf { law := 2424, dual := 1264, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2425, dual := 1410, proof := sorry })
                      (RArray.leaf { law := 2426, dual := 1338, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2427, dual := 1376, proof := sorry })
                      (RArray.leaf { law := 2428, dual := 1413, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2429, dual := 1256, proof := sorry })
                      (RArray.leaf { law := 2430, dual := 1395, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2431, dual := 1389, proof := sorry })
                      (RArray.leaf { law := 2432, dual := 1330, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2433, dual := 1398, proof := sorry })
                      (RArray.leaf { law := 2434, dual := 1273, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2435, dual := 1420, proof := sorry })
                      (RArray.leaf { law := 2436, dual := 1408, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2437, dual := 1381, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2438, dual := 1347, proof := sorry })
                      (RArray.leaf { law := 2439, dual := 1424, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2440, dual := 1019, proof := sorry })
                      (RArray.leaf { law := 2441, dual := 1071, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2442, dual := 1034, proof := sorry })
                      (RArray.leaf { law := 2443, dual := 1108, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2444, dual := 1145, proof := sorry })
                      (RArray.leaf { law := 2445, dual := 1024, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2446, dual := 1081, proof := sorry })
                      (RArray.leaf { law := 2447, dual := 1091, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2448, dual := 1044, proof := sorry })
                      (RArray.leaf { law := 2449, dual := 1118, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2450, dual := 1179, proof := sorry })
                      (RArray.leaf { law := 2451, dual := 1054, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2452, dual := 1162, proof := sorry })
                      (RArray.leaf { law := 2453, dual := 1128, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2454, dual := 1196, proof := sorry })
                      (RArray.leaf { law := 2455, dual := 1021, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2456, dual := 1074, proof := sorry })
                      (RArray.leaf { law := 2457, dual := 1077, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2458, dual := 1037, proof := sorry })
                      (RArray.leaf { law := 2459, dual := 1111, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2460, dual := 1153, proof := sorry })
                      (RArray.leaf { law := 2461, dual := 1040, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2462, dual := 1149, proof := sorry })
                      (RArray.leaf { law := 2463, dual := 1114, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2464, dual := 1157, proof := sorry })
                      (RArray.leaf { law := 2465, dual := 1027, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2466, dual := 1084, proof := sorry })
                      (RArray.leaf { law := 2467, dual := 1099, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2468, dual := 1047, proof := sorry })
                      (RArray.leaf { law := 2469, dual := 1121, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2470, dual := 1187, proof := sorry })
                      (RArray.leaf { law := 2471, dual := 1062, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2472, dual := 1166, proof := sorry })
                      (RArray.leaf { law := 2473, dual := 1136, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2474, dual := 1211, proof := sorry })
                      (RArray.leaf { law := 2475, dual := 1030, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2476, dual := 1095, proof := sorry })
                      (RArray.leaf { law := 2477, dual := 1087, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2478, dual := 1103, proof := sorry })
                      (RArray.leaf { law := 2479, dual := 1058, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2480, dual := 1132, proof := sorry })
                      (RArray.leaf { law := 2481, dual := 1170, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2482, dual := 1206, proof := sorry })
                      (RArray.leaf { law := 2483, dual := 1050, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2484, dual := 1183, proof := sorry })
                      (RArray.leaf { law := 2485, dual := 1124, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2486, dual := 1191, proof := sorry })
                      (RArray.leaf { law := 2487, dual := 1066, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2488, dual := 1201, proof := sorry })
                      (RArray.leaf { law := 2489, dual := 1174, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2490, dual := 1140, proof := sorry })
                      (RArray.leaf { law := 2491, dual := 1216, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2492, dual := 1020, proof := sorry })
                      (RArray.leaf { law := 2493, dual := 1072, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2494, dual := 1073, proof := sorry })
                      (RArray.leaf { law := 2495, dual := 1035, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2496, dual := 1109, proof := sorry })
                      (RArray.leaf { law := 2497, dual := 1147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2498, dual := 1036, proof := sorry })
                      (RArray.leaf { law := 2499, dual := 1146, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2500, dual := 1110, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2501, dual := 1148, proof := sorry })
                      (RArray.leaf { law := 2502, dual := 1025, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2503, dual := 1082, proof := sorry })
                      (RArray.leaf { law := 2504, dual := 1093, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2505, dual := 1045, proof := sorry })
                      (RArray.leaf { law := 2506, dual := 1119, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2507, dual := 1181, proof := sorry })
                      (RArray.leaf { law := 2508, dual := 1056, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2509, dual := 1163, proof := sorry })
                      (RArray.leaf { law := 2510, dual := 1130, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2511, dual := 1199, proof := sorry })
                      (RArray.leaf { law := 2512, dual := 1026, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2513, dual := 1092, proof := sorry })
                      (RArray.leaf { law := 2514, dual := 1083, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2515, dual := 1094, proof := sorry })
                      (RArray.leaf { law := 2516, dual := 1055, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2517, dual := 1129, proof := sorry })
                      (RArray.leaf { law := 2518, dual := 1164, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2519, dual := 1198, proof := sorry })
                      (RArray.leaf { law := 2520, dual := 1046, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2521, dual := 1180, proof := sorry })
                      (RArray.leaf { law := 2522, dual := 1120, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2523, dual := 1182, proof := sorry })
                      (RArray.leaf { law := 2524, dual := 1057, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2525, dual := 1197, proof := sorry })
                      (RArray.leaf { law := 2526, dual := 1165, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2527, dual := 1131, proof := sorry })
                      (RArray.leaf { law := 2528, dual := 1200, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2529, dual := 1022, proof := sorry })
                      (RArray.leaf { law := 2530, dual := 1075, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2531, dual := 1079, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2532, dual := 1038, proof := sorry })
                      (RArray.leaf { law := 2533, dual := 1112, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2534, dual := 1155, proof := sorry })
                      (RArray.leaf { law := 2535, dual := 1042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2536, dual := 1150, proof := sorry })
                      (RArray.leaf { law := 2537, dual := 1116, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2538, dual := 1160, proof := sorry })
                      (RArray.leaf { law := 2539, dual := 1028, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2540, dual := 1085, proof := sorry })
                      (RArray.leaf { law := 2541, dual := 1101, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2542, dual := 1048, proof := sorry })
                      (RArray.leaf { law := 2543, dual := 1122, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2544, dual := 1189, proof := sorry })
                      (RArray.leaf { law := 2545, dual := 1064, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2546, dual := 1167, proof := sorry })
                      (RArray.leaf { law := 2547, dual := 1138, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2548, dual := 1214, proof := sorry })
                      (RArray.leaf { law := 2549, dual := 1032, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2550, dual := 1096, proof := sorry })
                      (RArray.leaf { law := 2551, dual := 1089, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2552, dual := 1106, proof := sorry })
                      (RArray.leaf { law := 2553, dual := 1059, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2554, dual := 1133, proof := sorry })
                      (RArray.leaf { law := 2555, dual := 1172, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2556, dual := 1208, proof := sorry })
                      (RArray.leaf { law := 2557, dual := 1052, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2558, dual := 1184, proof := sorry })
                      (RArray.leaf { law := 2559, dual := 1126, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2560, dual := 1194, proof := sorry })
                      (RArray.leaf { law := 2561, dual := 1069, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2562, dual := 1202, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2563, dual := 1177, proof := sorry })
                      (RArray.leaf { law := 2564, dual := 1143, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2565, dual := 1220, proof := sorry })
                      (RArray.leaf { law := 2566, dual := 1023, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2567, dual := 1078, proof := sorry })
                      (RArray.leaf { law := 2568, dual := 1076, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2569, dual := 1080, proof := sorry })
                      (RArray.leaf { law := 2570, dual := 1041, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2571, dual := 1115, proof := sorry })
                      (RArray.leaf { law := 2572, dual := 1151, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2573, dual := 1159, proof := sorry })
                      (RArray.leaf { law := 2574, dual := 1039, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2575, dual := 1154, proof := sorry })
                      (RArray.leaf { law := 2576, dual := 1113, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2577, dual := 1156, proof := sorry })
                      (RArray.leaf { law := 2578, dual := 1043, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2579, dual := 1158, proof := sorry })
                      (RArray.leaf { law := 2580, dual := 1152, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2581, dual := 1117, proof := sorry })
                      (RArray.leaf { law := 2582, dual := 1161, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2583, dual := 1031, proof := sorry })
                      (RArray.leaf { law := 2584, dual := 1088, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2585, dual := 1097, proof := sorry })
                      (RArray.leaf { law := 2586, dual := 1105, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2587, dual := 1051, proof := sorry })
                      (RArray.leaf { law := 2588, dual := 1125, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2589, dual := 1185, proof := sorry })
                      (RArray.leaf { law := 2590, dual := 1193, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2591, dual := 1060, proof := sorry })
                      (RArray.leaf { law := 2592, dual := 1171, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2593, dual := 1134, proof := sorry })
                      (RArray.leaf { law := 2594, dual := 1209, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2595, dual := 1068, proof := sorry })
                      (RArray.leaf { law := 2596, dual := 1175, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2597, dual := 1204, proof := sorry })
                      (RArray.leaf { law := 2598, dual := 1142, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2599, dual := 1219, proof := sorry })
                      (RArray.leaf { law := 2600, dual := 1029, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2601, dual := 1100, proof := sorry })
                      (RArray.leaf { law := 2602, dual := 1086, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2603, dual := 1102, proof := sorry })
                      (RArray.leaf { law := 2604, dual := 1063, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2605, dual := 1137, proof := sorry })
                      (RArray.leaf { law := 2606, dual := 1168, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2607, dual := 1213, proof := sorry })
                      (RArray.leaf { law := 2608, dual := 1049, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2609, dual := 1188, proof := sorry })
                      (RArray.leaf { law := 2610, dual := 1123, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2611, dual := 1190, proof := sorry })
                      (RArray.leaf { law := 2612, dual := 1065, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2613, dual := 1212, proof := sorry })
                      (RArray.leaf { law := 2614, dual := 1169, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2615, dual := 1139, proof := sorry })
                      (RArray.leaf { law := 2616, dual := 1215, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2617, dual := 1033, proof := sorry })
                      (RArray.leaf { law := 2618, dual := 1104, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2619, dual := 1098, proof := sorry })
                      (RArray.leaf { law := 2620, dual := 1090, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2621, dual := 1107, proof := sorry })
                      (RArray.leaf { law := 2622, dual := 1067, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2623, dual := 1141, proof := sorry })
                      (RArray.leaf { law := 2624, dual := 1203, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2625, dual := 1176, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2626, dual := 1218, proof := sorry })
                      (RArray.leaf { law := 2627, dual := 1061, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2628, dual := 1207, proof := sorry })
                      (RArray.leaf { law := 2629, dual := 1135, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2630, dual := 1173, proof := sorry })
                      (RArray.leaf { law := 2631, dual := 1210, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2632, dual := 1053, proof := sorry })
                      (RArray.leaf { law := 2633, dual := 1192, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2634, dual := 1186, proof := sorry })
                      (RArray.leaf { law := 2635, dual := 1127, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2636, dual := 1195, proof := sorry })
                      (RArray.leaf { law := 2637, dual := 1070, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2638, dual := 1217, proof := sorry })
                      (RArray.leaf { law := 2639, dual := 1205, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2640, dual := 1178, proof := sorry })
                      (RArray.leaf { law := 2641, dual := 1144, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2642, dual := 1221, proof := sorry })
                      (RArray.leaf { law := 2643, dual := 816, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2644, dual := 868, proof := sorry })
                      (RArray.leaf { law := 2645, dual := 831, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2646, dual := 905, proof := sorry })
                      (RArray.leaf { law := 2647, dual := 942, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2648, dual := 821, proof := sorry })
                      (RArray.leaf { law := 2649, dual := 878, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2650, dual := 888, proof := sorry })
                      (RArray.leaf { law := 2651, dual := 841, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2652, dual := 915, proof := sorry })
                      (RArray.leaf { law := 2653, dual := 976, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2654, dual := 851, proof := sorry })
                      (RArray.leaf { law := 2655, dual := 959, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2656, dual := 925, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2657, dual := 993, proof := sorry })
                      (RArray.leaf { law := 2658, dual := 818, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2659, dual := 871, proof := sorry })
                      (RArray.leaf { law := 2660, dual := 874, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2661, dual := 834, proof := sorry })
                      (RArray.leaf { law := 2662, dual := 908, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2663, dual := 950, proof := sorry })
                      (RArray.leaf { law := 2664, dual := 837, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2665, dual := 946, proof := sorry })
                      (RArray.leaf { law := 2666, dual := 911, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2667, dual := 954, proof := sorry })
                      (RArray.leaf { law := 2668, dual := 824, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2669, dual := 881, proof := sorry })
                      (RArray.leaf { law := 2670, dual := 896, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2671, dual := 844, proof := sorry })
                      (RArray.leaf { law := 2672, dual := 918, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2673, dual := 984, proof := sorry })
                      (RArray.leaf { law := 2674, dual := 859, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2675, dual := 963, proof := sorry })
                      (RArray.leaf { law := 2676, dual := 933, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2677, dual := 1008, proof := sorry })
                      (RArray.leaf { law := 2678, dual := 827, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2679, dual := 892, proof := sorry })
                      (RArray.leaf { law := 2680, dual := 884, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2681, dual := 900, proof := sorry })
                      (RArray.leaf { law := 2682, dual := 855, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2683, dual := 929, proof := sorry })
                      (RArray.leaf { law := 2684, dual := 967, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2685, dual := 1003, proof := sorry })
                      (RArray.leaf { law := 2686, dual := 847, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2687, dual := 980, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2688, dual := 921, proof := sorry })
                      (RArray.leaf { law := 2689, dual := 988, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2690, dual := 863, proof := sorry })
                      (RArray.leaf { law := 2691, dual := 998, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2692, dual := 971, proof := sorry })
                      (RArray.leaf { law := 2693, dual := 937, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2694, dual := 1013, proof := sorry })
                      (RArray.leaf { law := 2695, dual := 817, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2696, dual := 869, proof := sorry })
                      (RArray.leaf { law := 2697, dual := 870, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2698, dual := 832, proof := sorry })
                      (RArray.leaf { law := 2699, dual := 906, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2700, dual := 944, proof := sorry })
                      (RArray.leaf { law := 2701, dual := 833, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2702, dual := 943, proof := sorry })
                      (RArray.leaf { law := 2703, dual := 907, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2704, dual := 945, proof := sorry })
                      (RArray.leaf { law := 2705, dual := 822, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2706, dual := 879, proof := sorry })
                      (RArray.leaf { law := 2707, dual := 890, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2708, dual := 842, proof := sorry })
                      (RArray.leaf { law := 2709, dual := 916, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2710, dual := 978, proof := sorry })
                      (RArray.leaf { law := 2711, dual := 853, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2712, dual := 960, proof := sorry })
                      (RArray.leaf { law := 2713, dual := 927, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2714, dual := 996, proof := sorry })
                      (RArray.leaf { law := 2715, dual := 823, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2716, dual := 889, proof := sorry })
                      (RArray.leaf { law := 2717, dual := 880, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2718, dual := 891, proof := sorry })
                      (RArray.leaf { law := 2719, dual := 852, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2720, dual := 926, proof := sorry })
                      (RArray.leaf { law := 2721, dual := 961, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2722, dual := 995, proof := sorry })
                      (RArray.leaf { law := 2723, dual := 843, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2724, dual := 977, proof := sorry })
                      (RArray.leaf { law := 2725, dual := 917, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2726, dual := 979, proof := sorry })
                      (RArray.leaf { law := 2727, dual := 854, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2728, dual := 994, proof := sorry })
                      (RArray.leaf { law := 2729, dual := 962, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2730, dual := 928, proof := sorry })
                      (RArray.leaf { law := 2731, dual := 997, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2732, dual := 819, proof := sorry })
                      (RArray.leaf { law := 2733, dual := 872, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2734, dual := 876, proof := sorry })
                      (RArray.leaf { law := 2735, dual := 835, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2736, dual := 909, proof := sorry })
                      (RArray.leaf { law := 2737, dual := 952, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2738, dual := 839, proof := sorry })
                      (RArray.leaf { law := 2739, dual := 947, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2740, dual := 913, proof := sorry })
                      (RArray.leaf { law := 2741, dual := 957, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2742, dual := 825, proof := sorry })
                      (RArray.leaf { law := 2743, dual := 882, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2744, dual := 898, proof := sorry })
                      (RArray.leaf { law := 2745, dual := 845, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2746, dual := 919, proof := sorry })
                      (RArray.leaf { law := 2747, dual := 986, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2748, dual := 861, proof := sorry })
                      (RArray.leaf { law := 2749, dual := 964, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2750, dual := 935, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2751, dual := 1011, proof := sorry })
                      (RArray.leaf { law := 2752, dual := 829, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2753, dual := 893, proof := sorry })
                      (RArray.leaf { law := 2754, dual := 886, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2755, dual := 903, proof := sorry })
                      (RArray.leaf { law := 2756, dual := 856, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2757, dual := 930, proof := sorry })
                      (RArray.leaf { law := 2758, dual := 969, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2759, dual := 1005, proof := sorry })
                      (RArray.leaf { law := 2760, dual := 849, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2761, dual := 981, proof := sorry })
                      (RArray.leaf { law := 2762, dual := 923, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2763, dual := 991, proof := sorry })
                      (RArray.leaf { law := 2764, dual := 866, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2765, dual := 999, proof := sorry })
                      (RArray.leaf { law := 2766, dual := 974, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2767, dual := 940, proof := sorry })
                      (RArray.leaf { law := 2768, dual := 1017, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2769, dual := 820, proof := sorry })
                      (RArray.leaf { law := 2770, dual := 875, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2771, dual := 873, proof := sorry })
                      (RArray.leaf { law := 2772, dual := 877, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2773, dual := 838, proof := sorry })
                      (RArray.leaf { law := 2774, dual := 912, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2775, dual := 948, proof := sorry })
                      (RArray.leaf { law := 2776, dual := 956, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2777, dual := 836, proof := sorry })
                      (RArray.leaf { law := 2778, dual := 951, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2779, dual := 910, proof := sorry })
                      (RArray.leaf { law := 2780, dual := 953, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2781, dual := 840, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2782, dual := 955, proof := sorry })
                      (RArray.leaf { law := 2783, dual := 949, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2784, dual := 914, proof := sorry })
                      (RArray.leaf { law := 2785, dual := 958, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2786, dual := 828, proof := sorry })
                      (RArray.leaf { law := 2787, dual := 885, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2788, dual := 894, proof := sorry })
                      (RArray.leaf { law := 2789, dual := 902, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2790, dual := 848, proof := sorry })
                      (RArray.leaf { law := 2791, dual := 922, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2792, dual := 982, proof := sorry })
                      (RArray.leaf { law := 2793, dual := 990, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2794, dual := 857, proof := sorry })
                      (RArray.leaf { law := 2795, dual := 968, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2796, dual := 931, proof := sorry })
                      (RArray.leaf { law := 2797, dual := 1006, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2798, dual := 865, proof := sorry })
                      (RArray.leaf { law := 2799, dual := 972, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2800, dual := 1001, proof := sorry })
                      (RArray.leaf { law := 2801, dual := 939, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2802, dual := 1016, proof := sorry })
                      (RArray.leaf { law := 2803, dual := 826, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2804, dual := 897, proof := sorry })
                      (RArray.leaf { law := 2805, dual := 883, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2806, dual := 899, proof := sorry })
                      (RArray.leaf { law := 2807, dual := 860, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2808, dual := 934, proof := sorry })
                      (RArray.leaf { law := 2809, dual := 965, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2810, dual := 1010, proof := sorry })
                      (RArray.leaf { law := 2811, dual := 846, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2812, dual := 985, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2813, dual := 920, proof := sorry })
                      (RArray.leaf { law := 2814, dual := 987, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2815, dual := 862, proof := sorry })
                      (RArray.leaf { law := 2816, dual := 1009, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2817, dual := 966, proof := sorry })
                      (RArray.leaf { law := 2818, dual := 936, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2819, dual := 1012, proof := sorry })
                      (RArray.leaf { law := 2820, dual := 830, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2821, dual := 901, proof := sorry })
                      (RArray.leaf { law := 2822, dual := 895, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2823, dual := 887, proof := sorry })
                      (RArray.leaf { law := 2824, dual := 904, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2825, dual := 864, proof := sorry })
                      (RArray.leaf { law := 2826, dual := 938, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2827, dual := 1000, proof := sorry })
                      (RArray.leaf { law := 2828, dual := 973, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2829, dual := 1015, proof := sorry })
                      (RArray.leaf { law := 2830, dual := 858, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2831, dual := 1004, proof := sorry })
                      (RArray.leaf { law := 2832, dual := 932, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2833, dual := 970, proof := sorry })
                      (RArray.leaf { law := 2834, dual := 1007, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2835, dual := 850, proof := sorry })
                      (RArray.leaf { law := 2836, dual := 989, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2837, dual := 983, proof := sorry })
                      (RArray.leaf { law := 2838, dual := 924, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2839, dual := 992, proof := sorry })
                      (RArray.leaf { law := 2840, dual := 867, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2841, dual := 1014, proof := sorry })
                      (RArray.leaf { law := 2842, dual := 1002, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2843, dual := 975, proof := sorry })
                      (RArray.leaf { law := 2844, dual := 941, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2845, dual := 1018, proof := sorry })
                      (RArray.leaf { law := 2846, dual := 613, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2847, dual := 665, proof := sorry })
                      (RArray.leaf { law := 2848, dual := 628, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2849, dual := 702, proof := sorry })
                      (RArray.leaf { law := 2850, dual := 739, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2851, dual := 618, proof := sorry })
                      (RArray.leaf { law := 2852, dual := 675, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2853, dual := 685, proof := sorry })
                      (RArray.leaf { law := 2854, dual := 638, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2855, dual := 712, proof := sorry })
                      (RArray.leaf { law := 2856, dual := 773, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2857, dual := 648, proof := sorry })
                      (RArray.leaf { law := 2858, dual := 756, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2859, dual := 722, proof := sorry })
                      (RArray.leaf { law := 2860, dual := 790, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2861, dual := 615, proof := sorry })
                      (RArray.leaf { law := 2862, dual := 668, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2863, dual := 671, proof := sorry })
                      (RArray.leaf { law := 2864, dual := 631, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2865, dual := 705, proof := sorry })
                      (RArray.leaf { law := 2866, dual := 747, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2867, dual := 634, proof := sorry })
                      (RArray.leaf { law := 2868, dual := 743, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2869, dual := 708, proof := sorry })
                      (RArray.leaf { law := 2870, dual := 751, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2871, dual := 621, proof := sorry })
                      (RArray.leaf { law := 2872, dual := 678, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2873, dual := 693, proof := sorry })
                      (RArray.leaf { law := 2874, dual := 641, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2875, dual := 715, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2876, dual := 781, proof := sorry })
                      (RArray.leaf { law := 2877, dual := 656, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2878, dual := 760, proof := sorry })
                      (RArray.leaf { law := 2879, dual := 730, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2880, dual := 805, proof := sorry })
                      (RArray.leaf { law := 2881, dual := 624, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2882, dual := 689, proof := sorry })
                      (RArray.leaf { law := 2883, dual := 681, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2884, dual := 697, proof := sorry })
                      (RArray.leaf { law := 2885, dual := 652, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2886, dual := 726, proof := sorry })
                      (RArray.leaf { law := 2887, dual := 764, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2888, dual := 800, proof := sorry })
                      (RArray.leaf { law := 2889, dual := 644, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2890, dual := 777, proof := sorry })
                      (RArray.leaf { law := 2891, dual := 718, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2892, dual := 785, proof := sorry })
                      (RArray.leaf { law := 2893, dual := 660, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2894, dual := 795, proof := sorry })
                      (RArray.leaf { law := 2895, dual := 768, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2896, dual := 734, proof := sorry })
                      (RArray.leaf { law := 2897, dual := 810, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2898, dual := 614, proof := sorry })
                      (RArray.leaf { law := 2899, dual := 666, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2900, dual := 667, proof := sorry })
                      (RArray.leaf { law := 2901, dual := 629, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2902, dual := 703, proof := sorry })
                      (RArray.leaf { law := 2903, dual := 741, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2904, dual := 630, proof := sorry })
                      (RArray.leaf { law := 2905, dual := 740, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2906, dual := 704, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2907, dual := 742, proof := sorry })
                      (RArray.leaf { law := 2908, dual := 619, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2909, dual := 676, proof := sorry })
                      (RArray.leaf { law := 2910, dual := 687, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2911, dual := 639, proof := sorry })
                      (RArray.leaf { law := 2912, dual := 713, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2913, dual := 775, proof := sorry })
                      (RArray.leaf { law := 2914, dual := 650, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2915, dual := 757, proof := sorry })
                      (RArray.leaf { law := 2916, dual := 724, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2917, dual := 793, proof := sorry })
                      (RArray.leaf { law := 2918, dual := 620, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2919, dual := 686, proof := sorry })
                      (RArray.leaf { law := 2920, dual := 677, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2921, dual := 688, proof := sorry })
                      (RArray.leaf { law := 2922, dual := 649, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2923, dual := 723, proof := sorry })
                      (RArray.leaf { law := 2924, dual := 758, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2925, dual := 792, proof := sorry })
                      (RArray.leaf { law := 2926, dual := 640, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2927, dual := 774, proof := sorry })
                      (RArray.leaf { law := 2928, dual := 714, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2929, dual := 776, proof := sorry })
                      (RArray.leaf { law := 2930, dual := 651, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2931, dual := 791, proof := sorry })
                      (RArray.leaf { law := 2932, dual := 759, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2933, dual := 725, proof := sorry })
                      (RArray.leaf { law := 2934, dual := 794, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2935, dual := 616, proof := sorry })
                      (RArray.leaf { law := 2936, dual := 669, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 2937, dual := 673, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 2938, dual := 632, proof := sorry })
                      (RArray.leaf { law := 2939, dual := 706, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2940, dual := 749, proof := sorry })
                      (RArray.leaf { law := 2941, dual := 636, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2942, dual := 744, proof := sorry })
                      (RArray.leaf { law := 2943, dual := 710, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2944, dual := 754, proof := sorry })
                      (RArray.leaf { law := 2945, dual := 622, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2946, dual := 679, proof := sorry })
                      (RArray.leaf { law := 2947, dual := 695, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2948, dual := 642, proof := sorry })
                      (RArray.leaf { law := 2949, dual := 716, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2950, dual := 783, proof := sorry })
                      (RArray.leaf { law := 2951, dual := 658, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2952, dual := 761, proof := sorry })
                      (RArray.leaf { law := 2953, dual := 732, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2954, dual := 808, proof := sorry })
                      (RArray.leaf { law := 2955, dual := 626, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2956, dual := 690, proof := sorry })
                      (RArray.leaf { law := 2957, dual := 683, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2958, dual := 700, proof := sorry })
                      (RArray.leaf { law := 2959, dual := 653, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2960, dual := 727, proof := sorry })
                      (RArray.leaf { law := 2961, dual := 766, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2962, dual := 802, proof := sorry })
                      (RArray.leaf { law := 2963, dual := 646, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2964, dual := 778, proof := sorry })
                      (RArray.leaf { law := 2965, dual := 720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2966, dual := 788, proof := sorry })
                      (RArray.leaf { law := 2967, dual := 663, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2968, dual := 796, proof := sorry })
                      (RArray.leaf { law := 2969, dual := 771, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2970, dual := 737, proof := sorry })
                      (RArray.leaf { law := 2971, dual := 814, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2972, dual := 617, proof := sorry })
                      (RArray.leaf { law := 2973, dual := 672, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2974, dual := 670, proof := sorry })
                      (RArray.leaf { law := 2975, dual := 674, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2976, dual := 635, proof := sorry })
                      (RArray.leaf { law := 2977, dual := 709, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2978, dual := 745, proof := sorry })
                      (RArray.leaf { law := 2979, dual := 753, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2980, dual := 633, proof := sorry })
                      (RArray.leaf { law := 2981, dual := 748, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2982, dual := 707, proof := sorry })
                      (RArray.leaf { law := 2983, dual := 750, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2984, dual := 637, proof := sorry })
                      (RArray.leaf { law := 2985, dual := 752, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2986, dual := 746, proof := sorry })
                      (RArray.leaf { law := 2987, dual := 711, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2988, dual := 755, proof := sorry })
                      (RArray.leaf { law := 2989, dual := 625, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2990, dual := 682, proof := sorry })
                      (RArray.leaf { law := 2991, dual := 691, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2992, dual := 699, proof := sorry })
                      (RArray.leaf { law := 2993, dual := 645, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2994, dual := 719, proof := sorry })
                      (RArray.leaf { law := 2995, dual := 779, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 2996, dual := 787, proof := sorry })
                      (RArray.leaf { law := 2997, dual := 654, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 2998, dual := 765, proof := sorry })
                      (RArray.leaf { law := 2999, dual := 728, proof := sorry })))))))))))
  (RArray.branch 500
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3000, dual := 803, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3001, dual := 662, proof := sorry })
                      (RArray.leaf { law := 3002, dual := 769, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3003, dual := 798, proof := sorry })
                      (RArray.leaf { law := 3004, dual := 736, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3005, dual := 813, proof := sorry })
                      (RArray.leaf { law := 3006, dual := 623, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3007, dual := 694, proof := sorry })
                      (RArray.leaf { law := 3008, dual := 680, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3009, dual := 696, proof := sorry })
                      (RArray.leaf { law := 3010, dual := 657, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3011, dual := 731, proof := sorry })
                      (RArray.leaf { law := 3012, dual := 762, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3013, dual := 807, proof := sorry })
                      (RArray.leaf { law := 3014, dual := 643, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3015, dual := 782, proof := sorry })
                      (RArray.leaf { law := 3016, dual := 717, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3017, dual := 784, proof := sorry })
                      (RArray.leaf { law := 3018, dual := 659, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3019, dual := 806, proof := sorry })
                      (RArray.leaf { law := 3020, dual := 763, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3021, dual := 733, proof := sorry })
                      (RArray.leaf { law := 3022, dual := 809, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3023, dual := 627, proof := sorry })
                      (RArray.leaf { law := 3024, dual := 698, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3025, dual := 692, proof := sorry })
                      (RArray.leaf { law := 3026, dual := 684, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3027, dual := 701, proof := sorry })
                      (RArray.leaf { law := 3028, dual := 661, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3029, dual := 735, proof := sorry })
                      (RArray.leaf { law := 3030, dual := 797, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3031, dual := 770, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3032, dual := 812, proof := sorry })
                      (RArray.leaf { law := 3033, dual := 655, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3034, dual := 801, proof := sorry })
                      (RArray.leaf { law := 3035, dual := 729, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3036, dual := 767, proof := sorry })
                      (RArray.leaf { law := 3037, dual := 804, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3038, dual := 647, proof := sorry })
                      (RArray.leaf { law := 3039, dual := 786, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3040, dual := 780, proof := sorry })
                      (RArray.leaf { law := 3041, dual := 721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3042, dual := 789, proof := sorry })
                      (RArray.leaf { law := 3043, dual := 664, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3044, dual := 811, proof := sorry })
                      (RArray.leaf { law := 3045, dual := 799, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3046, dual := 772, proof := sorry })
                      (RArray.leaf { law := 3047, dual := 738, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3048, dual := 815, proof := sorry })
                      (RArray.leaf { law := 3049, dual := 410, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3050, dual := 462, proof := sorry })
                      (RArray.leaf { law := 3051, dual := 425, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3052, dual := 499, proof := sorry })
                      (RArray.leaf { law := 3053, dual := 536, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3054, dual := 415, proof := sorry })
                      (RArray.leaf { law := 3055, dual := 472, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3056, dual := 482, proof := sorry })
                      (RArray.leaf { law := 3057, dual := 435, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3058, dual := 509, proof := sorry })
                      (RArray.leaf { law := 3059, dual := 570, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3060, dual := 445, proof := sorry })
                      (RArray.leaf { law := 3061, dual := 553, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3062, dual := 519, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3063, dual := 587, proof := sorry })
                      (RArray.leaf { law := 3064, dual := 412, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3065, dual := 465, proof := sorry })
                      (RArray.leaf { law := 3066, dual := 468, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3067, dual := 428, proof := sorry })
                      (RArray.leaf { law := 3068, dual := 502, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3069, dual := 544, proof := sorry })
                      (RArray.leaf { law := 3070, dual := 431, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3071, dual := 540, proof := sorry })
                      (RArray.leaf { law := 3072, dual := 505, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3073, dual := 548, proof := sorry })
                      (RArray.leaf { law := 3074, dual := 418, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3075, dual := 475, proof := sorry })
                      (RArray.leaf { law := 3076, dual := 490, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3077, dual := 438, proof := sorry })
                      (RArray.leaf { law := 3078, dual := 512, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3079, dual := 578, proof := sorry })
                      (RArray.leaf { law := 3080, dual := 453, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3081, dual := 557, proof := sorry })
                      (RArray.leaf { law := 3082, dual := 527, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3083, dual := 602, proof := sorry })
                      (RArray.leaf { law := 3084, dual := 421, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3085, dual := 486, proof := sorry })
                      (RArray.leaf { law := 3086, dual := 478, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3087, dual := 494, proof := sorry })
                      (RArray.leaf { law := 3088, dual := 449, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3089, dual := 523, proof := sorry })
                      (RArray.leaf { law := 3090, dual := 561, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3091, dual := 597, proof := sorry })
                      (RArray.leaf { law := 3092, dual := 441, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3093, dual := 574, proof := sorry })
                      (RArray.leaf { law := 3094, dual := 515, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3095, dual := 582, proof := sorry })
                      (RArray.leaf { law := 3096, dual := 457, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3097, dual := 592, proof := sorry })
                      (RArray.leaf { law := 3098, dual := 565, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3099, dual := 531, proof := sorry })
                      (RArray.leaf { law := 3100, dual := 607, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3101, dual := 411, proof := sorry })
                      (RArray.leaf { law := 3102, dual := 463, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3103, dual := 464, proof := sorry })
                      (RArray.leaf { law := 3104, dual := 426, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3105, dual := 500, proof := sorry })
                      (RArray.leaf { law := 3106, dual := 538, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3107, dual := 427, proof := sorry })
                      (RArray.leaf { law := 3108, dual := 537, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3109, dual := 501, proof := sorry })
                      (RArray.leaf { law := 3110, dual := 539, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3111, dual := 416, proof := sorry })
                      (RArray.leaf { law := 3112, dual := 473, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3113, dual := 484, proof := sorry })
                      (RArray.leaf { law := 3114, dual := 436, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3115, dual := 510, proof := sorry })
                      (RArray.leaf { law := 3116, dual := 572, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3117, dual := 447, proof := sorry })
                      (RArray.leaf { law := 3118, dual := 554, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3119, dual := 521, proof := sorry })
                      (RArray.leaf { law := 3120, dual := 590, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3121, dual := 417, proof := sorry })
                      (RArray.leaf { law := 3122, dual := 483, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3123, dual := 474, proof := sorry })
                      (RArray.leaf { law := 3124, dual := 485, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3125, dual := 446, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3126, dual := 520, proof := sorry })
                      (RArray.leaf { law := 3127, dual := 555, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3128, dual := 589, proof := sorry })
                      (RArray.leaf { law := 3129, dual := 437, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3130, dual := 571, proof := sorry })
                      (RArray.leaf { law := 3131, dual := 511, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3132, dual := 573, proof := sorry })
                      (RArray.leaf { law := 3133, dual := 448, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3134, dual := 588, proof := sorry })
                      (RArray.leaf { law := 3135, dual := 556, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3136, dual := 522, proof := sorry })
                      (RArray.leaf { law := 3137, dual := 591, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3138, dual := 413, proof := sorry })
                      (RArray.leaf { law := 3139, dual := 466, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3140, dual := 470, proof := sorry })
                      (RArray.leaf { law := 3141, dual := 429, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3142, dual := 503, proof := sorry })
                      (RArray.leaf { law := 3143, dual := 546, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3144, dual := 433, proof := sorry })
                      (RArray.leaf { law := 3145, dual := 541, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3146, dual := 507, proof := sorry })
                      (RArray.leaf { law := 3147, dual := 551, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3148, dual := 419, proof := sorry })
                      (RArray.leaf { law := 3149, dual := 476, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3150, dual := 492, proof := sorry })
                      (RArray.leaf { law := 3151, dual := 439, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3152, dual := 513, proof := sorry })
                      (RArray.leaf { law := 3153, dual := 580, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3154, dual := 455, proof := sorry })
                      (RArray.leaf { law := 3155, dual := 558, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3156, dual := 529, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3157, dual := 605, proof := sorry })
                      (RArray.leaf { law := 3158, dual := 423, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3159, dual := 487, proof := sorry })
                      (RArray.leaf { law := 3160, dual := 480, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3161, dual := 497, proof := sorry })
                      (RArray.leaf { law := 3162, dual := 450, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3163, dual := 524, proof := sorry })
                      (RArray.leaf { law := 3164, dual := 563, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3165, dual := 599, proof := sorry })
                      (RArray.leaf { law := 3166, dual := 443, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3167, dual := 575, proof := sorry })
                      (RArray.leaf { law := 3168, dual := 517, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3169, dual := 585, proof := sorry })
                      (RArray.leaf { law := 3170, dual := 460, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3171, dual := 593, proof := sorry })
                      (RArray.leaf { law := 3172, dual := 568, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3173, dual := 534, proof := sorry })
                      (RArray.leaf { law := 3174, dual := 611, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3175, dual := 414, proof := sorry })
                      (RArray.leaf { law := 3176, dual := 469, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3177, dual := 467, proof := sorry })
                      (RArray.leaf { law := 3178, dual := 471, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3179, dual := 432, proof := sorry })
                      (RArray.leaf { law := 3180, dual := 506, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3181, dual := 542, proof := sorry })
                      (RArray.leaf { law := 3182, dual := 550, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3183, dual := 430, proof := sorry })
                      (RArray.leaf { law := 3184, dual := 545, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3185, dual := 504, proof := sorry })
                      (RArray.leaf { law := 3186, dual := 547, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3187, dual := 434, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3188, dual := 549, proof := sorry })
                      (RArray.leaf { law := 3189, dual := 543, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3190, dual := 508, proof := sorry })
                      (RArray.leaf { law := 3191, dual := 552, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3192, dual := 422, proof := sorry })
                      (RArray.leaf { law := 3193, dual := 479, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3194, dual := 488, proof := sorry })
                      (RArray.leaf { law := 3195, dual := 496, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3196, dual := 442, proof := sorry })
                      (RArray.leaf { law := 3197, dual := 516, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3198, dual := 576, proof := sorry })
                      (RArray.leaf { law := 3199, dual := 584, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3200, dual := 451, proof := sorry })
                      (RArray.leaf { law := 3201, dual := 562, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3202, dual := 525, proof := sorry })
                      (RArray.leaf { law := 3203, dual := 600, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3204, dual := 459, proof := sorry })
                      (RArray.leaf { law := 3205, dual := 566, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3206, dual := 595, proof := sorry })
                      (RArray.leaf { law := 3207, dual := 533, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3208, dual := 610, proof := sorry })
                      (RArray.leaf { law := 3209, dual := 420, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3210, dual := 491, proof := sorry })
                      (RArray.leaf { law := 3211, dual := 477, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3212, dual := 493, proof := sorry })
                      (RArray.leaf { law := 3213, dual := 454, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3214, dual := 528, proof := sorry })
                      (RArray.leaf { law := 3215, dual := 559, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3216, dual := 604, proof := sorry })
                      (RArray.leaf { law := 3217, dual := 440, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3218, dual := 579, proof := sorry })
                      (RArray.leaf { law := 3219, dual := 514, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3220, dual := 581, proof := sorry })
                      (RArray.leaf { law := 3221, dual := 456, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3222, dual := 603, proof := sorry })
                      (RArray.leaf { law := 3223, dual := 560, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3224, dual := 530, proof := sorry })
                      (RArray.leaf { law := 3225, dual := 606, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3226, dual := 424, proof := sorry })
                      (RArray.leaf { law := 3227, dual := 495, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3228, dual := 489, proof := sorry })
                      (RArray.leaf { law := 3229, dual := 481, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3230, dual := 498, proof := sorry })
                      (RArray.leaf { law := 3231, dual := 458, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3232, dual := 532, proof := sorry })
                      (RArray.leaf { law := 3233, dual := 594, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3234, dual := 567, proof := sorry })
                      (RArray.leaf { law := 3235, dual := 609, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3236, dual := 452, proof := sorry })
                      (RArray.leaf { law := 3237, dual := 598, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3238, dual := 526, proof := sorry })
                      (RArray.leaf { law := 3239, dual := 564, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3240, dual := 601, proof := sorry })
                      (RArray.leaf { law := 3241, dual := 444, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3242, dual := 583, proof := sorry })
                      (RArray.leaf { law := 3243, dual := 577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3244, dual := 518, proof := sorry })
                      (RArray.leaf { law := 3245, dual := 586, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3246, dual := 461, proof := sorry })
                      (RArray.leaf { law := 3247, dual := 608, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3248, dual := 596, proof := sorry })
                      (RArray.leaf { law := 3249, dual := 569, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3250, dual := 535, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3251, dual := 612, proof := sorry })
                      (RArray.leaf { law := 3252, dual := 4064, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3253, dual := 4079, proof := sorry })
                      (RArray.leaf { law := 3254, dual := 4069, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3255, dual := 4089, proof := sorry })
                      (RArray.leaf { law := 3256, dual := 4099, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3257, dual := 4066, proof := sorry })
                      (RArray.leaf { law := 3258, dual := 4082, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3259, dual := 4085, proof := sorry })
                      (RArray.leaf { law := 3260, dual := 4072, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3261, dual := 4092, proof := sorry })
                      (RArray.leaf { law := 3262, dual := 4107, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3263, dual := 4075, proof := sorry })
                      (RArray.leaf { law := 3264, dual := 4103, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3265, dual := 4095, proof := sorry })
                      (RArray.leaf { law := 3266, dual := 4111, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3267, dual := 4065, proof := sorry })
                      (RArray.leaf { law := 3268, dual := 4080, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3269, dual := 4081, proof := sorry })
                      (RArray.leaf { law := 3270, dual := 4070, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3271, dual := 4090, proof := sorry })
                      (RArray.leaf { law := 3272, dual := 4101, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3273, dual := 4071, proof := sorry })
                      (RArray.leaf { law := 3274, dual := 4100, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3275, dual := 4091, proof := sorry })
                      (RArray.leaf { law := 3276, dual := 4102, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3277, dual := 4067, proof := sorry })
                      (RArray.leaf { law := 3278, dual := 4083, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3279, dual := 4087, proof := sorry })
                      (RArray.leaf { law := 3280, dual := 4073, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3281, dual := 4093, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3282, dual := 4109, proof := sorry })
                      (RArray.leaf { law := 3283, dual := 4077, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3284, dual := 4104, proof := sorry })
                      (RArray.leaf { law := 3285, dual := 4097, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3286, dual := 4114, proof := sorry })
                      (RArray.leaf { law := 3287, dual := 4068, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3288, dual := 4086, proof := sorry })
                      (RArray.leaf { law := 3289, dual := 4084, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3290, dual := 4088, proof := sorry })
                      (RArray.leaf { law := 3291, dual := 4076, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3292, dual := 4096, proof := sorry })
                      (RArray.leaf { law := 3293, dual := 4105, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3294, dual := 4113, proof := sorry })
                      (RArray.leaf { law := 3295, dual := 4074, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3296, dual := 4108, proof := sorry })
                      (RArray.leaf { law := 3297, dual := 4094, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3298, dual := 4110, proof := sorry })
                      (RArray.leaf { law := 3299, dual := 4078, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3300, dual := 4112, proof := sorry })
                      (RArray.leaf { law := 3301, dual := 4106, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3302, dual := 4098, proof := sorry })
                      (RArray.leaf { law := 3303, dual := 4115, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3304, dual := 4167, proof := sorry })
                      (RArray.leaf { law := 3305, dual := 4130, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3306, dual := 4212, proof := sorry })
                      (RArray.leaf { law := 3307, dual := 4157, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3308, dual := 4120, proof := sorry })
                      (RArray.leaf { law := 3309, dual := 4195, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3310, dual := 4178, proof := sorry })
                      (RArray.leaf { law := 3311, dual := 4141, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3312, dual := 4229, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3313, dual := 4247, proof := sorry })
                      (RArray.leaf { law := 3314, dual := 4164, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3315, dual := 4127, proof := sorry })
                      (RArray.leaf { law := 3316, dual := 4208, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3317, dual := 4154, proof := sorry })
                      (RArray.leaf { law := 3318, dual := 4117, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3319, dual := 4191, proof := sorry })
                      (RArray.leaf { law := 3320, dual := 4174, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3321, dual := 4137, proof := sorry })
                      (RArray.leaf { law := 3322, dual := 4225, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3323, dual := 4242, proof := sorry })
                      (RArray.leaf { law := 3324, dual := 4170, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3325, dual := 4133, proof := sorry })
                      (RArray.leaf { law := 3326, dual := 4216, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3327, dual := 4220, proof := sorry })
                      (RArray.leaf { law := 3328, dual := 4160, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3329, dual := 4123, proof := sorry })
                      (RArray.leaf { law := 3330, dual := 4199, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3331, dual := 4203, proof := sorry })
                      (RArray.leaf { law := 3332, dual := 4182, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3333, dual := 4145, proof := sorry })
                      (RArray.leaf { law := 3334, dual := 4233, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3335, dual := 4257, proof := sorry })
                      (RArray.leaf { law := 3336, dual := 4186, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3337, dual := 4149, proof := sorry })
                      (RArray.leaf { law := 3338, dual := 4252, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3339, dual := 4237, proof := sorry })
                      (RArray.leaf { law := 3340, dual := 4262, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3341, dual := 4166, proof := sorry })
                      (RArray.leaf { law := 3342, dual := 4129, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3343, dual := 4211, proof := sorry })
                      (RArray.leaf { law := 3344, dual := 4156, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3345, dual := 4119, proof := sorry })
                      (RArray.leaf { law := 3346, dual := 4194, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3347, dual := 4177, proof := sorry })
                      (RArray.leaf { law := 3348, dual := 4140, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3349, dual := 4228, proof := sorry })
                      (RArray.leaf { law := 3350, dual := 4246, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3351, dual := 4163, proof := sorry })
                      (RArray.leaf { law := 3352, dual := 4126, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3353, dual := 4207, proof := sorry })
                      (RArray.leaf { law := 3354, dual := 4153, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3355, dual := 4116, proof := sorry })
                      (RArray.leaf { law := 3356, dual := 4190, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3357, dual := 4173, proof := sorry })
                      (RArray.leaf { law := 3358, dual := 4136, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3359, dual := 4224, proof := sorry })
                      (RArray.leaf { law := 3360, dual := 4241, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3361, dual := 4169, proof := sorry })
                      (RArray.leaf { law := 3362, dual := 4132, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3363, dual := 4215, proof := sorry })
                      (RArray.leaf { law := 3364, dual := 4219, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3365, dual := 4159, proof := sorry })
                      (RArray.leaf { law := 3366, dual := 4122, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3367, dual := 4198, proof := sorry })
                      (RArray.leaf { law := 3368, dual := 4202, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3369, dual := 4181, proof := sorry })
                      (RArray.leaf { law := 3370, dual := 4144, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3371, dual := 4232, proof := sorry })
                      (RArray.leaf { law := 3372, dual := 4256, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3373, dual := 4185, proof := sorry })
                      (RArray.leaf { law := 3374, dual := 4148, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3375, dual := 4251, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3376, dual := 4236, proof := sorry })
                      (RArray.leaf { law := 3377, dual := 4261, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3378, dual := 4168, proof := sorry })
                      (RArray.leaf { law := 3379, dual := 4131, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3380, dual := 4213, proof := sorry })
                      (RArray.leaf { law := 3381, dual := 4214, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3382, dual := 4158, proof := sorry })
                      (RArray.leaf { law := 3383, dual := 4121, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3384, dual := 4196, proof := sorry })
                      (RArray.leaf { law := 3385, dual := 4197, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3386, dual := 4179, proof := sorry })
                      (RArray.leaf { law := 3387, dual := 4142, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3388, dual := 4230, proof := sorry })
                      (RArray.leaf { law := 3389, dual := 4249, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3390, dual := 4180, proof := sorry })
                      (RArray.leaf { law := 3391, dual := 4143, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3392, dual := 4248, proof := sorry })
                      (RArray.leaf { law := 3393, dual := 4231, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3394, dual := 4250, proof := sorry })
                      (RArray.leaf { law := 3395, dual := 4165, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3396, dual := 4128, proof := sorry })
                      (RArray.leaf { law := 3397, dual := 4209, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3398, dual := 4210, proof := sorry })
                      (RArray.leaf { law := 3399, dual := 4155, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3400, dual := 4118, proof := sorry })
                      (RArray.leaf { law := 3401, dual := 4192, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3402, dual := 4193, proof := sorry })
                      (RArray.leaf { law := 3403, dual := 4175, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3404, dual := 4138, proof := sorry })
                      (RArray.leaf { law := 3405, dual := 4226, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3406, dual := 4244, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3407, dual := 4176, proof := sorry })
                      (RArray.leaf { law := 3408, dual := 4139, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3409, dual := 4243, proof := sorry })
                      (RArray.leaf { law := 3410, dual := 4227, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3411, dual := 4245, proof := sorry })
                      (RArray.leaf { law := 3412, dual := 4171, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3413, dual := 4134, proof := sorry })
                      (RArray.leaf { law := 3414, dual := 4217, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3415, dual := 4222, proof := sorry })
                      (RArray.leaf { law := 3416, dual := 4161, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3417, dual := 4124, proof := sorry })
                      (RArray.leaf { law := 3418, dual := 4200, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3419, dual := 4205, proof := sorry })
                      (RArray.leaf { law := 3420, dual := 4183, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3421, dual := 4146, proof := sorry })
                      (RArray.leaf { law := 3422, dual := 4234, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3423, dual := 4259, proof := sorry })
                      (RArray.leaf { law := 3424, dual := 4188, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3425, dual := 4151, proof := sorry })
                      (RArray.leaf { law := 3426, dual := 4253, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3427, dual := 4239, proof := sorry })
                      (RArray.leaf { law := 3428, dual := 4265, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3429, dual := 4172, proof := sorry })
                      (RArray.leaf { law := 3430, dual := 4135, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3431, dual := 4221, proof := sorry })
                      (RArray.leaf { law := 3432, dual := 4218, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3433, dual := 4223, proof := sorry })
                      (RArray.leaf { law := 3434, dual := 4162, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3435, dual := 4125, proof := sorry })
                      (RArray.leaf { law := 3436, dual := 4204, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3437, dual := 4201, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3438, dual := 4206, proof := sorry })
                      (RArray.leaf { law := 3439, dual := 4187, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3440, dual := 4150, proof := sorry })
                      (RArray.leaf { law := 3441, dual := 4238, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3442, dual := 4254, proof := sorry })
                      (RArray.leaf { law := 3443, dual := 4264, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3444, dual := 4184, proof := sorry })
                      (RArray.leaf { law := 3445, dual := 4147, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3446, dual := 4258, proof := sorry })
                      (RArray.leaf { law := 3447, dual := 4235, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3448, dual := 4260, proof := sorry })
                      (RArray.leaf { law := 3449, dual := 4189, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3450, dual := 4152, proof := sorry })
                      (RArray.leaf { law := 3451, dual := 4263, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3452, dual := 4255, proof := sorry })
                      (RArray.leaf { law := 3453, dual := 4240, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3454, dual := 4266, proof := sorry })
                      (RArray.leaf { law := 3455, dual := 3861, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3456, dual := 3876, proof := sorry })
                      (RArray.leaf { law := 3457, dual := 3866, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3458, dual := 3886, proof := sorry })
                      (RArray.leaf { law := 3459, dual := 3896, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3460, dual := 3863, proof := sorry })
                      (RArray.leaf { law := 3461, dual := 3879, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3462, dual := 3882, proof := sorry })
                      (RArray.leaf { law := 3463, dual := 3869, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3464, dual := 3889, proof := sorry })
                      (RArray.leaf { law := 3465, dual := 3904, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3466, dual := 3872, proof := sorry })
                      (RArray.leaf { law := 3467, dual := 3900, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3468, dual := 3892, proof := sorry })
                      (RArray.leaf { law := 3469, dual := 3908, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3470, dual := 3862, proof := sorry })
                      (RArray.leaf { law := 3471, dual := 3877, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3472, dual := 3878, proof := sorry })
                      (RArray.leaf { law := 3473, dual := 3867, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3474, dual := 3887, proof := sorry })
                      (RArray.leaf { law := 3475, dual := 3898, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3476, dual := 3868, proof := sorry })
                      (RArray.leaf { law := 3477, dual := 3897, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3478, dual := 3888, proof := sorry })
                      (RArray.leaf { law := 3479, dual := 3899, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3480, dual := 3864, proof := sorry })
                      (RArray.leaf { law := 3481, dual := 3880, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3482, dual := 3884, proof := sorry })
                      (RArray.leaf { law := 3483, dual := 3870, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3484, dual := 3890, proof := sorry })
                      (RArray.leaf { law := 3485, dual := 3906, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3486, dual := 3874, proof := sorry })
                      (RArray.leaf { law := 3487, dual := 3901, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3488, dual := 3894, proof := sorry })
                      (RArray.leaf { law := 3489, dual := 3911, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3490, dual := 3865, proof := sorry })
                      (RArray.leaf { law := 3491, dual := 3883, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3492, dual := 3881, proof := sorry })
                      (RArray.leaf { law := 3493, dual := 3885, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3494, dual := 3873, proof := sorry })
                      (RArray.leaf { law := 3495, dual := 3893, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3496, dual := 3902, proof := sorry })
                      (RArray.leaf { law := 3497, dual := 3910, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3498, dual := 3871, proof := sorry })
                      (RArray.leaf { law := 3499, dual := 3905, proof := sorry }))))))))))
    (RArray.branch 250
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3500, dual := 3891, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3501, dual := 3907, proof := sorry })
                      (RArray.leaf { law := 3502, dual := 3875, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3503, dual := 3909, proof := sorry })
                      (RArray.leaf { law := 3504, dual := 3903, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3505, dual := 3895, proof := sorry })
                      (RArray.leaf { law := 3506, dual := 3912, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3507, dual := 3964, proof := sorry })
                      (RArray.leaf { law := 3508, dual := 3927, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3509, dual := 4009, proof := sorry })
                      (RArray.leaf { law := 3510, dual := 3954, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3511, dual := 3917, proof := sorry })
                      (RArray.leaf { law := 3512, dual := 3992, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3513, dual := 3975, proof := sorry })
                      (RArray.leaf { law := 3514, dual := 3938, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3515, dual := 4026, proof := sorry })
                      (RArray.leaf { law := 3516, dual := 4044, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3517, dual := 3961, proof := sorry })
                      (RArray.leaf { law := 3518, dual := 3924, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3519, dual := 4005, proof := sorry })
                      (RArray.leaf { law := 3520, dual := 3951, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3521, dual := 3914, proof := sorry })
                      (RArray.leaf { law := 3522, dual := 3988, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3523, dual := 3971, proof := sorry })
                      (RArray.leaf { law := 3524, dual := 3934, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3525, dual := 4022, proof := sorry })
                      (RArray.leaf { law := 3526, dual := 4039, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3527, dual := 3967, proof := sorry })
                      (RArray.leaf { law := 3528, dual := 3930, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3529, dual := 4013, proof := sorry })
                      (RArray.leaf { law := 3530, dual := 4017, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3531, dual := 3957, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3532, dual := 3920, proof := sorry })
                      (RArray.leaf { law := 3533, dual := 3996, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3534, dual := 4000, proof := sorry })
                      (RArray.leaf { law := 3535, dual := 3979, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3536, dual := 3942, proof := sorry })
                      (RArray.leaf { law := 3537, dual := 4030, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3538, dual := 4054, proof := sorry })
                      (RArray.leaf { law := 3539, dual := 3983, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3540, dual := 3946, proof := sorry })
                      (RArray.leaf { law := 3541, dual := 4049, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3542, dual := 4034, proof := sorry })
                      (RArray.leaf { law := 3543, dual := 4059, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3544, dual := 3963, proof := sorry })
                      (RArray.leaf { law := 3545, dual := 3926, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3546, dual := 4008, proof := sorry })
                      (RArray.leaf { law := 3547, dual := 3953, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3548, dual := 3916, proof := sorry })
                      (RArray.leaf { law := 3549, dual := 3991, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3550, dual := 3974, proof := sorry })
                      (RArray.leaf { law := 3551, dual := 3937, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3552, dual := 4025, proof := sorry })
                      (RArray.leaf { law := 3553, dual := 4043, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3554, dual := 3960, proof := sorry })
                      (RArray.leaf { law := 3555, dual := 3923, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3556, dual := 4004, proof := sorry })
                      (RArray.leaf { law := 3557, dual := 3950, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3558, dual := 3913, proof := sorry })
                      (RArray.leaf { law := 3559, dual := 3987, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3560, dual := 3970, proof := sorry })
                      (RArray.leaf { law := 3561, dual := 3933, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3562, dual := 4021, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3563, dual := 4038, proof := sorry })
                      (RArray.leaf { law := 3564, dual := 3966, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3565, dual := 3929, proof := sorry })
                      (RArray.leaf { law := 3566, dual := 4012, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3567, dual := 4016, proof := sorry })
                      (RArray.leaf { law := 3568, dual := 3956, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3569, dual := 3919, proof := sorry })
                      (RArray.leaf { law := 3570, dual := 3995, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3571, dual := 3999, proof := sorry })
                      (RArray.leaf { law := 3572, dual := 3978, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3573, dual := 3941, proof := sorry })
                      (RArray.leaf { law := 3574, dual := 4029, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3575, dual := 4053, proof := sorry })
                      (RArray.leaf { law := 3576, dual := 3982, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3577, dual := 3945, proof := sorry })
                      (RArray.leaf { law := 3578, dual := 4048, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3579, dual := 4033, proof := sorry })
                      (RArray.leaf { law := 3580, dual := 4058, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3581, dual := 3965, proof := sorry })
                      (RArray.leaf { law := 3582, dual := 3928, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3583, dual := 4010, proof := sorry })
                      (RArray.leaf { law := 3584, dual := 4011, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3585, dual := 3955, proof := sorry })
                      (RArray.leaf { law := 3586, dual := 3918, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3587, dual := 3993, proof := sorry })
                      (RArray.leaf { law := 3588, dual := 3994, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3589, dual := 3976, proof := sorry })
                      (RArray.leaf { law := 3590, dual := 3939, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3591, dual := 4027, proof := sorry })
                      (RArray.leaf { law := 3592, dual := 4046, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3593, dual := 3977, proof := sorry })
                      (RArray.leaf { law := 3594, dual := 3940, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3595, dual := 4045, proof := sorry })
                      (RArray.leaf { law := 3596, dual := 4028, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3597, dual := 4047, proof := sorry })
                      (RArray.leaf { law := 3598, dual := 3962, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3599, dual := 3925, proof := sorry })
                      (RArray.leaf { law := 3600, dual := 4006, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3601, dual := 4007, proof := sorry })
                      (RArray.leaf { law := 3602, dual := 3952, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3603, dual := 3915, proof := sorry })
                      (RArray.leaf { law := 3604, dual := 3989, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3605, dual := 3990, proof := sorry })
                      (RArray.leaf { law := 3606, dual := 3972, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3607, dual := 3935, proof := sorry })
                      (RArray.leaf { law := 3608, dual := 4023, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3609, dual := 4041, proof := sorry })
                      (RArray.leaf { law := 3610, dual := 3973, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3611, dual := 3936, proof := sorry })
                      (RArray.leaf { law := 3612, dual := 4040, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3613, dual := 4024, proof := sorry })
                      (RArray.leaf { law := 3614, dual := 4042, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3615, dual := 3968, proof := sorry })
                      (RArray.leaf { law := 3616, dual := 3931, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3617, dual := 4014, proof := sorry })
                      (RArray.leaf { law := 3618, dual := 4019, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3619, dual := 3958, proof := sorry })
                      (RArray.leaf { law := 3620, dual := 3921, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3621, dual := 3997, proof := sorry })
                      (RArray.leaf { law := 3622, dual := 4002, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3623, dual := 3980, proof := sorry })
                      (RArray.leaf { law := 3624, dual := 3943, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3625, dual := 4031, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3626, dual := 4056, proof := sorry })
                      (RArray.leaf { law := 3627, dual := 3985, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3628, dual := 3948, proof := sorry })
                      (RArray.leaf { law := 3629, dual := 4050, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3630, dual := 4036, proof := sorry })
                      (RArray.leaf { law := 3631, dual := 4062, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3632, dual := 3969, proof := sorry })
                      (RArray.leaf { law := 3633, dual := 3932, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3634, dual := 4018, proof := sorry })
                      (RArray.leaf { law := 3635, dual := 4015, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3636, dual := 4020, proof := sorry })
                      (RArray.leaf { law := 3637, dual := 3959, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3638, dual := 3922, proof := sorry })
                      (RArray.leaf { law := 3639, dual := 4001, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3640, dual := 3998, proof := sorry })
                      (RArray.leaf { law := 3641, dual := 4003, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3642, dual := 3984, proof := sorry })
                      (RArray.leaf { law := 3643, dual := 3947, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3644, dual := 4035, proof := sorry })
                      (RArray.leaf { law := 3645, dual := 4051, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3646, dual := 4061, proof := sorry })
                      (RArray.leaf { law := 3647, dual := 3981, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3648, dual := 3944, proof := sorry })
                      (RArray.leaf { law := 3649, dual := 4055, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3650, dual := 4032, proof := sorry })
                      (RArray.leaf { law := 3651, dual := 4057, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3652, dual := 3986, proof := sorry })
                      (RArray.leaf { law := 3653, dual := 3949, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3654, dual := 4060, proof := sorry })
                      (RArray.leaf { law := 3655, dual := 4052, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3656, dual := 4037, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3657, dual := 4063, proof := sorry })
                      (RArray.leaf { law := 3658, dual := 3658, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3659, dual := 3673, proof := sorry })
                      (RArray.leaf { law := 3660, dual := 3663, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3661, dual := 3683, proof := sorry })
                      (RArray.leaf { law := 3662, dual := 3693, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3663, dual := 3660, proof := sorry })
                      (RArray.leaf { law := 3664, dual := 3676, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3665, dual := 3679, proof := sorry })
                      (RArray.leaf { law := 3666, dual := 3666, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3667, dual := 3686, proof := sorry })
                      (RArray.leaf { law := 3668, dual := 3701, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3669, dual := 3669, proof := sorry })
                      (RArray.leaf { law := 3670, dual := 3697, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3671, dual := 3689, proof := sorry })
                      (RArray.leaf { law := 3672, dual := 3705, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3673, dual := 3659, proof := sorry })
                      (RArray.leaf { law := 3674, dual := 3674, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3675, dual := 3675, proof := sorry })
                      (RArray.leaf { law := 3676, dual := 3664, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3677, dual := 3684, proof := sorry })
                      (RArray.leaf { law := 3678, dual := 3695, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3679, dual := 3665, proof := sorry })
                      (RArray.leaf { law := 3680, dual := 3694, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3681, dual := 3685, proof := sorry })
                      (RArray.leaf { law := 3682, dual := 3696, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3683, dual := 3661, proof := sorry })
                      (RArray.leaf { law := 3684, dual := 3677, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3685, dual := 3681, proof := sorry })
                      (RArray.leaf { law := 3686, dual := 3667, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3687, dual := 3687, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3688, dual := 3703, proof := sorry })
                      (RArray.leaf { law := 3689, dual := 3671, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3690, dual := 3698, proof := sorry })
                      (RArray.leaf { law := 3691, dual := 3691, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3692, dual := 3708, proof := sorry })
                      (RArray.leaf { law := 3693, dual := 3662, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3694, dual := 3680, proof := sorry })
                      (RArray.leaf { law := 3695, dual := 3678, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3696, dual := 3682, proof := sorry })
                      (RArray.leaf { law := 3697, dual := 3670, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3698, dual := 3690, proof := sorry })
                      (RArray.leaf { law := 3699, dual := 3699, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3700, dual := 3707, proof := sorry })
                      (RArray.leaf { law := 3701, dual := 3668, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3702, dual := 3702, proof := sorry })
                      (RArray.leaf { law := 3703, dual := 3688, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3704, dual := 3704, proof := sorry })
                      (RArray.leaf { law := 3705, dual := 3672, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3706, dual := 3706, proof := sorry })
                      (RArray.leaf { law := 3707, dual := 3700, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3708, dual := 3692, proof := sorry })
                      (RArray.leaf { law := 3709, dual := 3709, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3710, dual := 3761, proof := sorry })
                      (RArray.leaf { law := 3711, dual := 3724, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3712, dual := 3806, proof := sorry })
                      (RArray.leaf { law := 3713, dual := 3751, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3714, dual := 3714, proof := sorry })
                      (RArray.leaf { law := 3715, dual := 3789, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3716, dual := 3772, proof := sorry })
                      (RArray.leaf { law := 3717, dual := 3735, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3718, dual := 3823, proof := sorry })
                      (RArray.leaf { law := 3719, dual := 3841, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3720, dual := 3758, proof := sorry })
                      (RArray.leaf { law := 3721, dual := 3721, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3722, dual := 3802, proof := sorry })
                      (RArray.leaf { law := 3723, dual := 3748, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3724, dual := 3711, proof := sorry })
                      (RArray.leaf { law := 3725, dual := 3785, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3726, dual := 3768, proof := sorry })
                      (RArray.leaf { law := 3727, dual := 3731, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3728, dual := 3819, proof := sorry })
                      (RArray.leaf { law := 3729, dual := 3836, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3730, dual := 3764, proof := sorry })
                      (RArray.leaf { law := 3731, dual := 3727, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3732, dual := 3810, proof := sorry })
                      (RArray.leaf { law := 3733, dual := 3814, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3734, dual := 3754, proof := sorry })
                      (RArray.leaf { law := 3735, dual := 3717, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3736, dual := 3793, proof := sorry })
                      (RArray.leaf { law := 3737, dual := 3797, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3738, dual := 3776, proof := sorry })
                      (RArray.leaf { law := 3739, dual := 3739, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3740, dual := 3827, proof := sorry })
                      (RArray.leaf { law := 3741, dual := 3851, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3742, dual := 3780, proof := sorry })
                      (RArray.leaf { law := 3743, dual := 3743, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3744, dual := 3846, proof := sorry })
                      (RArray.leaf { law := 3745, dual := 3831, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3746, dual := 3856, proof := sorry })
                      (RArray.leaf { law := 3747, dual := 3760, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3748, dual := 3723, proof := sorry })
                      (RArray.leaf { law := 3749, dual := 3805, proof := sorry })))))))))
      (RArray.branch 125
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3750, dual := 3750, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3751, dual := 3713, proof := sorry })
                      (RArray.leaf { law := 3752, dual := 3788, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3753, dual := 3771, proof := sorry })
                      (RArray.leaf { law := 3754, dual := 3734, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3755, dual := 3822, proof := sorry })
                      (RArray.leaf { law := 3756, dual := 3840, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3757, dual := 3757, proof := sorry })
                      (RArray.leaf { law := 3758, dual := 3720, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3759, dual := 3801, proof := sorry })
                      (RArray.leaf { law := 3760, dual := 3747, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3761, dual := 3710, proof := sorry })
                      (RArray.leaf { law := 3762, dual := 3784, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3763, dual := 3767, proof := sorry })
                      (RArray.leaf { law := 3764, dual := 3730, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3765, dual := 3818, proof := sorry })
                      (RArray.leaf { law := 3766, dual := 3835, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3767, dual := 3763, proof := sorry })
                      (RArray.leaf { law := 3768, dual := 3726, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3769, dual := 3809, proof := sorry })
                      (RArray.leaf { law := 3770, dual := 3813, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3771, dual := 3753, proof := sorry })
                      (RArray.leaf { law := 3772, dual := 3716, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3773, dual := 3792, proof := sorry })
                      (RArray.leaf { law := 3774, dual := 3796, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3775, dual := 3775, proof := sorry })
                      (RArray.leaf { law := 3776, dual := 3738, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3777, dual := 3826, proof := sorry })
                      (RArray.leaf { law := 3778, dual := 3850, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3779, dual := 3779, proof := sorry })
                      (RArray.leaf { law := 3780, dual := 3742, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3781, dual := 3845, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3782, dual := 3830, proof := sorry })
                      (RArray.leaf { law := 3783, dual := 3855, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3784, dual := 3762, proof := sorry })
                      (RArray.leaf { law := 3785, dual := 3725, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3786, dual := 3807, proof := sorry })
                      (RArray.leaf { law := 3787, dual := 3808, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3788, dual := 3752, proof := sorry })
                      (RArray.leaf { law := 3789, dual := 3715, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3790, dual := 3790, proof := sorry })
                      (RArray.leaf { law := 3791, dual := 3791, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3792, dual := 3773, proof := sorry })
                      (RArray.leaf { law := 3793, dual := 3736, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3794, dual := 3824, proof := sorry })
                      (RArray.leaf { law := 3795, dual := 3843, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3796, dual := 3774, proof := sorry })
                      (RArray.leaf { law := 3797, dual := 3737, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3798, dual := 3842, proof := sorry })
                      (RArray.leaf { law := 3799, dual := 3825, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3800, dual := 3844, proof := sorry })
                      (RArray.leaf { law := 3801, dual := 3759, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3802, dual := 3722, proof := sorry })
                      (RArray.leaf { law := 3803, dual := 3803, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3804, dual := 3804, proof := sorry })
                      (RArray.leaf { law := 3805, dual := 3749, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3806, dual := 3712, proof := sorry })
                      (RArray.leaf { law := 3807, dual := 3786, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3808, dual := 3787, proof := sorry })
                      (RArray.leaf { law := 3809, dual := 3769, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3810, dual := 3732, proof := sorry })
                      (RArray.leaf { law := 3811, dual := 3820, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3812, dual := 3838, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3813, dual := 3770, proof := sorry })
                      (RArray.leaf { law := 3814, dual := 3733, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3815, dual := 3837, proof := sorry })
                      (RArray.leaf { law := 3816, dual := 3821, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3817, dual := 3839, proof := sorry })
                      (RArray.leaf { law := 3818, dual := 3765, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3819, dual := 3728, proof := sorry })
                      (RArray.leaf { law := 3820, dual := 3811, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3821, dual := 3816, proof := sorry })
                      (RArray.leaf { law := 3822, dual := 3755, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3823, dual := 3718, proof := sorry })
                      (RArray.leaf { law := 3824, dual := 3794, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3825, dual := 3799, proof := sorry })
                      (RArray.leaf { law := 3826, dual := 3777, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3827, dual := 3740, proof := sorry })
                      (RArray.leaf { law := 3828, dual := 3828, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3829, dual := 3853, proof := sorry })
                      (RArray.leaf { law := 3830, dual := 3782, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3831, dual := 3745, proof := sorry })
                      (RArray.leaf { law := 3832, dual := 3847, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3833, dual := 3833, proof := sorry })
                      (RArray.leaf { law := 3834, dual := 3859, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3835, dual := 3766, proof := sorry })
                      (RArray.leaf { law := 3836, dual := 3729, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3837, dual := 3815, proof := sorry })
                      (RArray.leaf { law := 3838, dual := 3812, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3839, dual := 3817, proof := sorry })
                      (RArray.leaf { law := 3840, dual := 3756, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3841, dual := 3719, proof := sorry })
                      (RArray.leaf { law := 3842, dual := 3798, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3843, dual := 3795, proof := sorry })
                      (RArray.leaf { law := 3844, dual := 3800, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3845, dual := 3781, proof := sorry })
                      (RArray.leaf { law := 3846, dual := 3744, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3847, dual := 3832, proof := sorry })
                      (RArray.leaf { law := 3848, dual := 3848, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3849, dual := 3858, proof := sorry })
                      (RArray.leaf { law := 3850, dual := 3778, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3851, dual := 3741, proof := sorry })
                      (RArray.leaf { law := 3852, dual := 3852, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3853, dual := 3829, proof := sorry })
                      (RArray.leaf { law := 3854, dual := 3854, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3855, dual := 3783, proof := sorry })
                      (RArray.leaf { law := 3856, dual := 3746, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3857, dual := 3857, proof := sorry })
                      (RArray.leaf { law := 3858, dual := 3849, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3859, dual := 3834, proof := sorry })
                      (RArray.leaf { law := 3860, dual := 3860, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3861, dual := 3455, proof := sorry })
                      (RArray.leaf { law := 3862, dual := 3470, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3863, dual := 3460, proof := sorry })
                      (RArray.leaf { law := 3864, dual := 3480, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3865, dual := 3490, proof := sorry })
                      (RArray.leaf { law := 3866, dual := 3457, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3867, dual := 3473, proof := sorry })
                      (RArray.leaf { law := 3868, dual := 3476, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3869, dual := 3463, proof := sorry })
                      (RArray.leaf { law := 3870, dual := 3483, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3871, dual := 3498, proof := sorry })
                      (RArray.leaf { law := 3872, dual := 3466, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3873, dual := 3494, proof := sorry })
                      (RArray.leaf { law := 3874, dual := 3486, proof := sorry }))))))))
        (RArray.branch 62
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3875, dual := 3502, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3876, dual := 3456, proof := sorry })
                      (RArray.leaf { law := 3877, dual := 3471, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3878, dual := 3472, proof := sorry })
                      (RArray.leaf { law := 3879, dual := 3461, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3880, dual := 3481, proof := sorry })
                      (RArray.leaf { law := 3881, dual := 3492, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3882, dual := 3462, proof := sorry })
                      (RArray.leaf { law := 3883, dual := 3491, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3884, dual := 3482, proof := sorry })
                      (RArray.leaf { law := 3885, dual := 3493, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3886, dual := 3458, proof := sorry })
                      (RArray.leaf { law := 3887, dual := 3474, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3888, dual := 3478, proof := sorry })
                      (RArray.leaf { law := 3889, dual := 3464, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3890, dual := 3484, proof := sorry })
                      (RArray.leaf { law := 3891, dual := 3500, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3892, dual := 3468, proof := sorry })
                      (RArray.leaf { law := 3893, dual := 3495, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3894, dual := 3488, proof := sorry })
                      (RArray.leaf { law := 3895, dual := 3505, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3896, dual := 3459, proof := sorry })
                      (RArray.leaf { law := 3897, dual := 3477, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3898, dual := 3475, proof := sorry })
                      (RArray.leaf { law := 3899, dual := 3479, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3900, dual := 3467, proof := sorry })
                      (RArray.leaf { law := 3901, dual := 3487, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3902, dual := 3496, proof := sorry })
                      (RArray.leaf { law := 3903, dual := 3504, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3904, dual := 3465, proof := sorry })
                      (RArray.leaf { law := 3905, dual := 3499, proof := sorry }))))))
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3906, dual := 3485, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3907, dual := 3501, proof := sorry })
                      (RArray.leaf { law := 3908, dual := 3469, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3909, dual := 3503, proof := sorry })
                      (RArray.leaf { law := 3910, dual := 3497, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3911, dual := 3489, proof := sorry })
                      (RArray.leaf { law := 3912, dual := 3506, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3913, dual := 3558, proof := sorry })
                      (RArray.leaf { law := 3914, dual := 3521, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3915, dual := 3603, proof := sorry })
                      (RArray.leaf { law := 3916, dual := 3548, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3917, dual := 3511, proof := sorry })
                      (RArray.leaf { law := 3918, dual := 3586, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3919, dual := 3569, proof := sorry })
                      (RArray.leaf { law := 3920, dual := 3532, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3921, dual := 3620, proof := sorry })
                      (RArray.leaf { law := 3922, dual := 3638, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3923, dual := 3555, proof := sorry })
                      (RArray.leaf { law := 3924, dual := 3518, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3925, dual := 3599, proof := sorry })
                      (RArray.leaf { law := 3926, dual := 3545, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3927, dual := 3508, proof := sorry })
                      (RArray.leaf { law := 3928, dual := 3582, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3929, dual := 3565, proof := sorry })
                      (RArray.leaf { law := 3930, dual := 3528, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3931, dual := 3616, proof := sorry })
                      (RArray.leaf { law := 3932, dual := 3633, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3933, dual := 3561, proof := sorry })
                      (RArray.leaf { law := 3934, dual := 3524, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3935, dual := 3607, proof := sorry })
                      (RArray.leaf { law := 3936, dual := 3611, proof := sorry })))))))
          (RArray.branch 31
            (RArray.branch 15
              (RArray.branch 7
                (RArray.branch 3
                  (RArray.branch 1 (RArray.leaf { law := 3937, dual := 3551, proof := sorry })
                    (RArray.branch 1 (RArray.leaf { law := 3938, dual := 3514, proof := sorry })
                      (RArray.leaf { law := 3939, dual := 3590, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3940, dual := 3594, proof := sorry })
                      (RArray.leaf { law := 3941, dual := 3573, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3942, dual := 3536, proof := sorry })
                      (RArray.leaf { law := 3943, dual := 3624, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3944, dual := 3648, proof := sorry })
                      (RArray.leaf { law := 3945, dual := 3577, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3946, dual := 3540, proof := sorry })
                      (RArray.leaf { law := 3947, dual := 3643, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3948, dual := 3628, proof := sorry })
                      (RArray.leaf { law := 3949, dual := 3653, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3950, dual := 3557, proof := sorry })
                      (RArray.leaf { law := 3951, dual := 3520, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3952, dual := 3602, proof := sorry })
                      (RArray.leaf { law := 3953, dual := 3547, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3954, dual := 3510, proof := sorry })
                      (RArray.leaf { law := 3955, dual := 3585, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3956, dual := 3568, proof := sorry })
                      (RArray.leaf { law := 3957, dual := 3531, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3958, dual := 3619, proof := sorry })
                      (RArray.leaf { law := 3959, dual := 3637, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3960, dual := 3554, proof := sorry })
                      (RArray.leaf { law := 3961, dual := 3517, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3962, dual := 3598, proof := sorry })
                      (RArray.leaf { law := 3963, dual := 3544, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3964, dual := 3507, proof := sorry })
                      (RArray.leaf { law := 3965, dual := 3581, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3966, dual := 3564, proof := sorry })
                      (RArray.leaf { law := 3967, dual := 3527, proof := sorry }))))))
            (RArray.branch 16
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3968, dual := 3615, proof := sorry })
                      (RArray.leaf { law := 3969, dual := 3632, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3970, dual := 3560, proof := sorry })
                      (RArray.leaf { law := 3971, dual := 3523, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3972, dual := 3606, proof := sorry })
                      (RArray.leaf { law := 3973, dual := 3610, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3974, dual := 3550, proof := sorry })
                      (RArray.leaf { law := 3975, dual := 3513, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3976, dual := 3589, proof := sorry })
                      (RArray.leaf { law := 3977, dual := 3593, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3978, dual := 3572, proof := sorry })
                      (RArray.leaf { law := 3979, dual := 3535, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3980, dual := 3623, proof := sorry })
                      (RArray.leaf { law := 3981, dual := 3647, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3982, dual := 3576, proof := sorry })
                      (RArray.leaf { law := 3983, dual := 3539, proof := sorry })))))
              (RArray.branch 8
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3984, dual := 3642, proof := sorry })
                      (RArray.leaf { law := 3985, dual := 3627, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3986, dual := 3652, proof := sorry })
                      (RArray.leaf { law := 3987, dual := 3559, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3988, dual := 3522, proof := sorry })
                      (RArray.leaf { law := 3989, dual := 3604, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3990, dual := 3605, proof := sorry })
                      (RArray.leaf { law := 3991, dual := 3549, proof := sorry }))))
                (RArray.branch 4
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3992, dual := 3512, proof := sorry })
                      (RArray.leaf { law := 3993, dual := 3587, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3994, dual := 3588, proof := sorry })
                      (RArray.leaf { law := 3995, dual := 3570, proof := sorry })))
                  (RArray.branch 2
                    (RArray.branch 1 (RArray.leaf { law := 3996, dual := 3533, proof := sorry })
                      (RArray.leaf { law := 3997, dual := 3621, proof := sorry }))
                    (RArray.branch 1 (RArray.leaf { law := 3998, dual := 3640, proof := sorry })
                      (RArray.leaf { law := 3999, dual := 3571, proof := sorry })))))))))))

end EndToEnd
