module DriversLicense where

data DriversLicense = DriversLicense
  [VehicleClass]
  String
  (Int, Int, Int)

data VehicleClass = A | B Bool | BE | C | D
