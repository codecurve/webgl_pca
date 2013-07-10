import Native.Graphics.WebGLScene as N
import Native.FastJSON as NJSON
import Dict
import Mouse
import Keyboard
import Touch

import Http (Success, Waiting, Failure)
import Json
import JavaScript.Experimental
import Graphics.Input (dropDown)
import JavaScript (fromList, toList)

data BasisFunction = CONSTANT | LINEAR_LAGRANGE | QUADRATIC_LAGRANGE |
                     CUBIC_LAGRANGE | LINEAR_SIMPLEX | QUADRATIC_SIMPLEX
type Element = Int
-- 3D cartesian coordinates.
data Coord3D = Coord3D Float Float Float
data Triangle = Triangle Coord3D Coord3D Coord3D
data Shape = LINE | SQUARE | TRIANGLE | CUBE | TETRAHEDRON | WEDGE12 | WEDGE13 | WEDGE23
type GLProjection = Matrix4x4
data GLColour = GLColour Float Float Float
data Vector4 = Vector4 Float Float Float Float
data Matrix4x4 = Matrix4x4 Vector4 Vector4 Vector4 Vector4
data Vector3 = Vector3 Float Float Float
data Quaternion = Quaternion Float Float Float Float

data GLPrimModel = GLPrimModel {
  -- A list of primitive triangles.
  primitives: [Triangle]
  }

data GLPrimSceneView = GLPrimSceneView {
  projection: GLProjection, -- A projection / camera matrix to apply.
  ambientColour: GLColour,  -- The ambient colour.
  diffuseColour: GLColour,  -- The diffuse light colour.
  ambientIntensity: Float,  -- The intensity in [0,1] of the ambient light.
  diffuseIntensity: Float,  -- The intensity in [0,1] of the diffuse light.
  diffuseDirection: Vector3 -- The diffuse light direction vector.
  }

-- Constructs a WebGL element to view a model according to settings.
glSceneObject : Int -> Int -> GLPrimModel -> GLPrimSceneView -> Element
glSceneObject = N.glSceneObject

-- Sends a request to return a raw JSString.
sendRaw : Signal Request -> Signal Response JSString
sendRaw = NJSON.send

-- Does a raw parse of a JSON JSString (no deep conversion).
fastJSON : JSString -> a
fastJSON = NJSON.fastJSON

-- Does a raw array or object lookup.
rawLookup : JSArray a -> Int -> a
rawLookup = NJSON.rawLookup

-- Remaps one JSArray using another as a mapping.
simpleRemapArray : JSArray { loc: Int, glob: Int } -> JSArray a -> JSArray a
simpleRemapArray = NJSON.simpleRemapArray

-- Remaps one JSArray as a linear combination of another.
linearRemapArray : JSArray { loc : Int, globs: JSArray { glob: Int, mup: Float }} -> JSArray Float -> JSArray Float
linearRemapArray = NJSON.linearRemapArray

trilinearInterpolate : (TrilinearLocalNode -> Float) -> Xi -> Float
trilinearInterpolate = NJSON.trilinearInterpolate
bicubicLinearInterpolate : (BicubicLinearLocalNode -> Float) -> Xi -> Float
bicubicLinearInterpolate = NJSON.bicubicLinearInterpolate

-- Some basic matrix maths specific to 4x4 matrices...
identity4x4 = Matrix4x4 (Vector4 1 0 0 0)
                        (Vector4 0 1 0 0)
                        (Vector4 0 0 1 0)
                        (Vector4 0 0 0 1)

vec4ToXYZ : Vector4 -> Vector3
vec4ToXYZ (Vector4 x y z _) = Vector3 x y z

matrix4x4Row : Int -> Matrix4x4 -> Vector4
matrix4x4Row row (Matrix4x4 r1 r2 r3 r4) =
  case row of
    0 -> r1
    1 -> r2
    2 -> r3
    3 -> r4

matrix4x4Column : Int -> Matrix4x4 -> Vector4
matrix4x4Column row (Matrix4x4 (Vector4 x11 x12 x13 x14)
                               (Vector4 x21 x22 x23 x24)
                               (Vector4 x31 x32 x33 x34)
                               (Vector4 x41 x42 x43 x44)) =
  case row of
    0 -> Vector4 x11 x21 x31 x41
    1 -> Vector4 x12 x22 x32 x42
    2 -> Vector4 x13 x23 x33 x43
    3 -> Vector4 x14 x24 x34 x44

dotProduct : Vector4 -> Vector4 -> Float
dotProduct (Vector4 x1 x2 x3 x4) (Vector4 y1 y2 y3 y4) =
  (x1*y1) + (x2*y2) + (x3*y3) + (x4*y4)

multiply4x4 : Matrix4x4 -> Matrix4x4 -> Matrix4x4
multiply4x4 m1 m2 =
  let
    p r c = dotProduct (matrix4x4Row r m1) (matrix4x4Column c m2)
  in
   Matrix4x4 (Vector4 (p 0 0) (p 0 1) (p 0 2) (p 0 3))
             (Vector4 (p 1 0) (p 1 1) (p 1 2) (p 1 3))
             (Vector4 (p 2 0) (p 2 1) (p 2 2) (p 2 3))
             (Vector4 (p 3 0) (p 3 1) (p 3 2) (p 3 3))

mat4x4xv : Matrix4x4 -> Vector4 -> Vector4
mat4x4xv m v =
  Vector4 (dotProduct (matrix4x4Row 0 m) v)
          (dotProduct (matrix4x4Row 1 m) v)
          (dotProduct (matrix4x4Row 2 m) v)
          (dotProduct (matrix4x4Row 3 m) v)

transpose4x4 : Matrix4x4 -> Matrix4x4
transpose4x4 (Matrix4x4 (Vector4 x11 x12 x13 x14)
                        (Vector4 x21 x22 x23 x24)
                        (Vector4 x31 x32 x33 x34)
                        (Vector4 x41 x42 x43 x44)) =
  Matrix4x4 (Vector4 x11 x21 x31 x41)
            (Vector4 x12 x22 x32 x42)
            (Vector4 x13 x23 x33 x43)
            (Vector4 x14 x24 x34 x44)

norm4 : Vector4 -> Vector3
norm4 (Vector4 x1 x2 x3 x4) = Vector3 (x1/x4) (x2/x4) (x3/x4)

-- | mat4ToInverseMat3 calculates the inverse of the upper 3x3 elements of a 4x4 matrix, returning a 4x4 matrix containing the result in its upper 3x3, and the identiy in the lower right.
--   Based on code from glMatrix.
mat4ToInverseMat3 : Matrix4x4 -> Matrix4x4
mat4ToInverseMat3 (Matrix4x4 (Vector4 x11 x12 x13 x14)
                             (Vector4 x21 x22 x23 x24)
                             (Vector4 x31 x32 x33 x34)
                             (Vector4 x41 x42 x43 x44)) =
  let
    b12 = x33*x22-x23*x32
    b22 = x23*x31-x33*x21
    b32 = x32*x21-x22*x31
    det = x11*b12 + x12*b22 + x13*b32
    invDet = if det == 0 then 0 else 1/det
  in
    Matrix4x4
      (Vector4 (b12*invDet) ((x13*x32 - x33*x12)*invDet) ((x23*x12 - x13*x22)*invDet) 0)
      (Vector4 (b22*invDet) ((x33*x11 - x13*x31)*invDet) ((x13*x21 - x23*x11)*invDet) 0)
      (Vector4 (b32*invDet) ((x12*x31 - x32*x11)*invDet) ((x22*x11 - x12*x21)*invDet) 0)
      (Vector4 0            0                            0                            1)

quaternionToRotationMatrix (Quaternion a b c d) =
  Matrix4x4 (Vector4 (1 - 2 * (c * c + d * d)) (2 * (b * c + a * d))     (2 * (b * d - a * c))     0)
            (Vector4 (2 * (b * c - a * d))     (1 - 2 * (b * b + d * d)) (2 * (c * d + a * b))     0)
            (Vector4 (2 * (b * d + a * c))     (2 * (c * d - a * b))     (1 - 2 * (b * b + c * c)) 0)
            (Vector4 0                         0                         0                         1)

normaliseQuaternion (Quaternion a b c d) =
  let
    norm = sqrt (a * a + b * b + c * c + d * d)
  in
   Quaternion (a/norm) (b/norm) (c/norm) (d/norm)
  
multiplyQuaternion (Quaternion a1 b1 c1 d1) (Quaternion a2 b2 c2 d2) =
  Quaternion (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2)
             (c1 * d2 - d1 * c2 + a1 * b2 + a2 * b1)
             (d1 * b2 - b1 * d2 + a1 * c2 + a2 * c1)
             (b1 * c2 - c1 * b2 + a1 * d2 + d1 * a2)
conjugateQuaternion (Quaternion a b c d) = Quaternion a (0-b) (0-c) (0-d)

rotateVectorByQuaternion : Quaternion -> Vector3 -> Vector3
rotateVectorByQuaternion q (Vector3 x y z) =
  let
    Quaternion _ x' y' z' =
      q `multiplyQuaternion` (Quaternion 0 x y z) `multiplyQuaternion` (conjugateQuaternion q)
  in
   Vector3 x' y' z'

eulerToQuaternion theta phi psi =
  let
    theta2 = theta / 2
    phi2 = phi / 2
    psi2 = psi / 2
    costheta2 = cos theta2
    sintheta2 = sin theta2
    cosphi2 = cos phi2
    sinphi2 = sin phi2
    cospsi2 = cos psi2
    sinpsi2 = sin psi2
  in
   Quaternion (cospsi2 * costheta2 * cosphi2 + sinpsi2 * costheta2 * cosphi2)
              (sinpsi2 * costheta2 * cosphi2 - cospsi2 * sintheta2 * sinphi2)
              (cospsi2 * sintheta2 * cosphi2 + sinpsi2 * costheta2 * sinphi2)
              (cospsi2 * costheta2 * sinphi2 - sinpsi2 * sintheta2 * cosphi2)

vectorToTranslationMatrix (Vector3 x y z) =
  Matrix4x4 (Vector4 1 0 0 x)
            (Vector4 0 1 0 y)
            (Vector4 0 0 1 z)
            (Vector4 0 0 0 1)

lowVal = 0-50
highVal = 50
lowZ = 0-50
highZ = 50

placeholderModel =
  let
    -- l = left, r = right, b = bottom, t = top, f = front, a = back.
    clbf = Coord3D lowVal lowVal lowZ
    crbf = Coord3D highVal lowVal lowZ
    cltf = Coord3D lowVal highVal lowZ
    crtf = Coord3D highVal highVal lowZ
    clba = Coord3D lowVal lowVal highZ
    crba = Coord3D highVal lowVal highZ
    clta = Coord3D lowVal highVal highZ
    crta = Coord3D highVal highVal highZ
    quad a b c d = [Triangle a b c, Triangle a c d]
  in
   GLPrimModel {
     -- Vertex ordering: anti-clockwise around external surface.
     primitives =
        quad clbf crbf crtf cltf ++ -- front
        quad clba clbf cltf clta ++ -- left
        quad crbf crba crta crtf ++ -- right
        quad clba clta crta crba ++ -- back
        quad cltf crtf crta clta ++ -- top
        quad crbf clbf clba crba ++ -- bottom
        []
               }

myFovRadians = pi / 4

perspectiveMatrix near far aspectRatio fovRadians =
  let
    f = 1.0 / (tan(fovRadians / 2))
    nf = 1 / (near - far)
  in
   Matrix4x4
     (Vector4 (f / aspectRatio) 0 0                   0)
     (Vector4 0                 f 0                   0)
     (Vector4 0                 0 ((far + near) * nf) ((2 * far * near) * nf))
     (Vector4 0                 0 (0-1)               0)

myPerspectiveMatrix : Matrix4x4
myPerspectiveMatrix = perspectiveMatrix 0.01 1000 1 myFovRadians

data TranslationPlane = TranslateXY | TranslateXZ
data CameraModifyMode = CameraRotate | CameraTranslate TranslationPlane

type CameraMoveState = { cameraQuaternion: Quaternion, cameraTransformation: Vector3 Float Float Float,
                         processedPosition: (Int, Int),
                         mainTouch: Touch, 
                         wasDragging: Bool, 
                         cameraModifyMode: CameraModifyMode, debug: [(String, Vector3)] }

initialCameraMoveState : CameraMoveState
initialCameraMoveState = { cameraQuaternion = Quaternion 1 0 0 0,
                           cameraTransformation = Vector3 0 0 (0-200),
                           processedPosition = (0,0), 
                           mainTouch = { x = 0, y = 0, id = 0, x0 = 0, y0 = 0, t0 = 0 },
                           wasDragging = False,
                           cameraModifyMode = CameraRotate, debug=[]
                           }

keyboardAlt : [KeyCode] -> Bool
keyboardAlt keysDown = any (\x -> x == 18) keysDown 

cameraMoveState : Signal CameraMoveState
cameraMoveState = Signal.foldp updateCameraMoveState initialCameraMoveState (Signal.lift4 (,,,) Keyboard.shift Keyboard.ctrl Keyboard.keysDown Touch.touches)

-- V1 = projection along Z axis onto positive hemisphere of unit sphere.
sphereProjectionZ3D : Float -> Float -> Vector3
sphereProjectionZ3D x y = 
  let
    z = sqrt ( max 0 ( 1 - (x * x) + (y * y) ) )
  in
    Vector3 x y z

crossV3xV3 : Vector3 -> Vector3 -> Vector3
crossV3xV3 (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = 
  Vector3
    ( (y1 * z2) - (z1 * y2) )
    ( (z1 * x2) - (x1 * z2) )
    ( (x1 * y2) - (y1 * x2) )

subtractV3fromV3 (Vector3 x1 y1 z1) (Vector3 x2 y2 z2) = 
  Vector3 (x2 - x1) (y2 - y1) (z2 - z1)
 
updateCameraMoveState : (Bool, Bool, [KeyCode], [Touch]) -> CameraMoveState -> CameraMoveState
updateCameraMoveState (shift, ctrl, keysDown, touches) oldMoveState =
  let
    dragging = (length touches > 0)
  in
    if not dragging
      then {oldMoveState | wasDragging <- False }
      else
        let
          newCameraModifyMode = if (shift || length touches == 2)                       then CameraTranslate TranslateXY else
                                if (ctrl || keyboardAlt keysDown || length touches > 2) then CameraTranslate TranslateXZ 
                                else CameraRotate
        in
          if not oldMoveState.wasDragging
            then
              let pointer = head touches in
                { oldMoveState | wasDragging <- True, processedPosition <- (pointer.x, pointer.y), mainTouch <- head touches,
                                cameraModifyMode <- newCameraModifyMode}
            else
              let
                previousPointCatcher = filter (\t -> t.id == oldMoveState.mainTouch.id ) touches
                pointer = if length previousPointCatcher > 0 then head previousPointCatcher else head touches
                (lastX, lastY) = oldMoveState.processedPosition
              in
                case oldMoveState.cameraModifyMode of
                  CameraRotate ->
                    let
                      -- all x,y,z coordinates will be normalised to coordinates in which the sphere of sphereRadius is a unit sphere
                      halfCanvasWidth  = (toFloat canvasWidth) /2
                      halfCanvasHeight = (toFloat canvasHeight)/2
                      px : Float
                      px = pointer.x
                      py : Float
                      py = pointer.y
                      sphereRadius =  maximum ( map abs [(toFloat lastX)-halfCanvasWidth, (toFloat lastY)-halfCanvasHeight, halfCanvasWidth, halfCanvasHeight, px-halfCanvasWidth, py-halfCanvasHeight] )
                      v1 = sphereProjectionZ3D (lastX     / sphereRadius - 1) (1 - (lastY     / sphereRadius ))
                      v2 = sphereProjectionZ3D (pointer.x / sphereRadius - 1) (1 - (pointer.y / sphereRadius ))

                      dv = subtractV3fromV3 v2 v1

                      -- Cross product: dv X V2 (Could also have used dV X V1)
                      (Vector3 rx ry rz) = crossV3xV3 v1 dv

                      -- rw is found so that it is the w coordinate of a normalised (i.e. unit length) quaternion.
                      rw = sqrt ( max 0 ( 1  - (rx * rx) + (ry * ry) + (rz * rz) ) )

                      -- Simple formula for rotation quaternion, since it is an infinitesimal rotation.
                      rotQuaternion = normaliseQuaternion (Quaternion rw rx ry rz) 
                    in
                      { oldMoveState | cameraQuaternion <-
                        normaliseQuaternion ( oldMoveState.cameraQuaternion `multiplyQuaternion` rotQuaternion ),
                        processedPosition <- (pointer.x, pointer.y), cameraModifyMode <- newCameraModifyMode, mainTouch <- pointer, 
                        debug <- [
                          ("lastX, lastY, 0", (Vector3 (toFloat lastX) (toFloat lastY) 0)),
                          ("cw/2, ch/2, 0", (Vector3 halfCanvasWidth halfCanvasHeight 0)),
                          ("sphereRadius rw 0", (Vector3 sphereRadius rw 0)),
                          ("rx ry rz", (Vector3 rx ry rz)),
                          ("v1",v1), ("v2",v2), ("dv", dv) ] }
                  CameraTranslate plane ->
                    let
                      distanceX = (toFloat (pointer.x - lastX)) / (toFloat canvasWidth) * 50
                      distanceY = (toFloat (pointer.y - lastY)) / (toFloat canvasHeight) * 50
                      translateBy = case plane of
                                      TranslateXY -> (distanceX, 0-distanceY, 0)
                                      TranslateXZ -> (distanceX, 0, distanceY)
                      Vector3 otx oty otz = oldMoveState.cameraTransformation
                      (tx, ty, tz) =  translateBy
                    in
                      { oldMoveState |
                          cameraTransformation <- Vector3 (otx + tx) (oty + ty) (otz + tz),
                          processedPosition <- (pointer.x, pointer.y), cameraModifyMode <- newCameraModifyMode, mainTouch <- pointer }

cameraMatrix : Signal Matrix4x4
cameraMatrix = lift (\x ->
  vectorToTranslationMatrix x.cameraTransformation
     `multiply4x4`
  quaternionToRotationMatrix x.cameraQuaternion
  ) cameraMoveState

type LVJSON =
  { localToGlobalMuTheta: JSArray {loc: Int, glob: Int},
    localToGlobalLambda: JSArray {loc: Int, globs: JSArray {glob: Int, mup: Float}},
    distributions: JSArray {dataset: JSString, coordScheme: JSString,
                            analysis: JSString,
                            biologicalState: JSString, components: Int,
                            averages: { flength: Float, lambdas: JSArray Float, mus: JSArray Float,
                                 thetas: JSArray Float}} }

responseToLVJSON : Response JSString -> Maybe LVJSON
responseToLVJSON resp = 
  case resp of
    Waiting -> Nothing
    Failure _ _ -> Nothing
    Success raw ->
      Just (fastJSON raw)

-- This identifies a parameter from the set of 40 parameters used for mu or lambda.
data GlobalMuLambda = GlobalMuLambda Int
-- This identifies a parameter from the set of 134 parameters used for theta.
data GlobalTheta = GlobalTheta Int

-- There are 16 elements in the LV model; this identifies one (1..16).
data ElementID = ElementID Int
-- There are 32 local nodes in the bicubic-linear interpolation (1..32)
-- Ordering: xi1 minor, xi3 major (e.g. first 4 nodes have same xi2,
--  first 16 nodes have the same xi3). Linear in xi3.
data BicubicLinearLocalNode = BicubicLinearLocalNode Int

-- There are 8 local nodes in the trilinear interpolation (1..16)
-- xi1 minor, xi3 major.
data TrilinearLocalNode = TrilinearLocalNode Int

-- There are two surfaces - endo and epicardial.
data Surface = Endocardial | Epicardial

-- For graphical purposes, we refine each element into (refineX-1)*(refineY-1) quads, each containing
-- refineX*refineY nodes. This identifies one of those nodes within an element (as a number in
-- [1,refineX*refineY]).
data RefinedNodeID = RefinedNodeID Int

-- A prolate spheriodal coordinate, given a fixed focal length.
data Prolate = Prolate { lambda: Float, mu: Float, theta: Float }
data Xi = Xi (Float, Float, Float)

refineX = 6
refineY = 6

canvasWidth : Int
canvasWidth = 500
canvasHeight : Int
canvasHeight = 500

initialDiffuseDirection = Vector4 (0-0.3) (0-0.5) (0-0.8) 1

lvJSON = lift responseToLVJSON (sendRaw (constant <| Http.get ("../LV.json")))

surfaceToFloat x = case x of
  Endocardial -> 0
  Epicardial -> 1

nElements = 16
nBicubicLinearLocalNodes = 32
nTrilinearLocalNodes = 8

localNodeIndexBicubicLinear : BicubicLinearLocalNode -> ElementID -> Int
localNodeIndexBicubicLinear (BicubicLinearLocalNode lnID) (ElementID elID) =
  (elID - 1) * nBicubicLinearLocalNodes + (lnID - 1) + 1

localNodeIndexTrilinear : TrilinearLocalNode -> ElementID -> Int
localNodeIndexTrilinear (TrilinearLocalNode lnID) (ElementID elID) =
  (elID - 1) * nTrilinearLocalNodes + (lnID - 1) + 1

allRefinedNodes : [RefinedNodeID]
allRefinedNodes = map RefinedNodeID [1..(refineX*refineY)]

allElements : [ElementID]
allElements = map ElementID [1..nElements]

allSurfaces : [Surface]
allSurfaces = [Endocardial, Epicardial]

refinedNodeToXiCoordinates : RefinedNodeID -> Surface -> Xi
refinedNodeToXiCoordinates (RefinedNodeID rnid) surf =
  let
    rnid0 = rnid - 1
    col = rnid0 `mod` refineX
    row = rnid `div` refineX
  in
   Xi ((toFloat col) * (1 / toFloat (refineX - 1)),
       (toFloat row) * (1 / toFloat (refineY - 1)),
       surfaceToFloat surf)

cosh : Float -> Float
cosh x = (exp x + exp (0-x)) * 0.5
sinh : Float -> Float
sinh x = (exp x - exp (0-x)) * 0.5

-- Converts prolate spheroidal to cartesian
prolateToCartesian : Float -> Prolate -> Coord3D
prolateToCartesian focalLength (Prolate { lambda, mu, theta }) =
  Coord3D (focalLength * cosh lambda * cos mu) (focalLength * sinh lambda * sin mu * cos theta)
          (focalLength * sinh lambda * sin mu * sin theta)

phaseCorrect : [Float] -> [Float]
phaseCorrect x = case x of
  (a::((b::_) as r)) -> if b - a > pi then (a + 2*pi)::(phaseCorrect r) else a::(phaseCorrect r)
  l -> l

lvJSONToModel : [ElementID] -> Maybe LVJSON -> GLPrimModel
lvJSONToModel showElems resp =
  case resp of
    Nothing -> placeholderModel
    Just rawData ->
      let
        localLambdas = linearRemapArray rawData.localToGlobalLambda
                              (rawLookup rawData.distributions 0).averages.lambdas
        localMus = simpleRemapArray rawData.localToGlobalMuTheta
                              (rawLookup rawData.distributions 0).averages.mus
        localThetas =
          fromList . phaseCorrect . toList <|
            simpleRemapArray rawData.localToGlobalMuTheta
              (rawLookup rawData.distributions 0).averages.thetas

        trilinearLookupValue values (ElementID elid) (TrilinearLocalNode ln) =
          rawLookup values ((elid - 1) * nTrilinearLocalNodes + (ln - 1))
        
        bicubicLinearLookupValue values (ElementID elid) (BicubicLinearLocalNode ln) =
          rawLookup values ((elid - 1) * nBicubicLinearLocalNodes + (ln - 1))
        
        lookupLambdaValue : ElementID -> BicubicLinearLocalNode -> Float
        lookupLambdaValue = bicubicLinearLookupValue localLambdas

        lookupMuValue : ElementID -> TrilinearLocalNode -> Float
        lookupMuValue =
          trilinearLookupValue localMus
        lookupThetaValue : ElementID -> TrilinearLocalNode -> Float
        lookupThetaValue = trilinearLookupValue localThetas

        {-
        doTrilinearInterpolation : (TrilinearLocalNode -> Float) -> Xi -> Float
        doTrilinearInterpolation f (Xi (xi0, xi1, xi2)) =
          sum <| map (
            \(sxi0, termxi0) -> sum <|
              map (
            \(sxi1, termxi1) -> sum <|
              map (\(sxi2, termxi2) ->
                (f (TrilinearLocalNode (sxi0 + sxi1 * 2 + sxi2 * 4 + 1))) * termxi0 * termxi1 * termxi2
                  )
                  [(0, 1 - xi2), (1, xi2)]
                  )
                  [(0, 1 - xi1), (1, xi1)]
                    )
                [(0, 1 - xi0), (1, xi0)]
        doBicubicLinearInterpolation : (BicubicLinearLocalNode -> Float) -> Xi -> Float
        doBicubicLinearInterpolation f (Xi (xi0, xi1, xi2)) =
          let xiFunc xi =
             let xi2 = xi * xi
                 xi3 = xi2 * xi
             in [(0, 1-3*xi+3*xi2-xi3), (1, 3*xi-6*xi2 +3*xi3),
                 (2, 3 * xi2 - 3 * xi3), (3, xi3)]
          in
            sum <| map (
              \(sxi0, termxi0) -> sum <|
                map (
              \(sxi1, termxi1) -> sum <|
                map (\(sxi2, termxi2) ->
                  (f (BicubicLinearLocalNode (sxi0 + sxi1 * 4 + sxi2 * 16 + 1))) * termxi0 * termxi1 * termxi2
                    )
                    [(0, 1 - xi2), (1, xi2)]
                    )
                    (xiFunc xi1)
                      )
                      (xiFunc xi0)

        -}
        

        prolateCoords : ElementID -> Surface -> RefinedNodeID -> Prolate
        prolateCoords elid surf rnid =
          let
            xi = refinedNodeToXiCoordinates rnid surf
          in
            Prolate { lambda = bicubicLinearInterpolate (lookupLambdaValue elid) xi,
                      mu = trilinearInterpolate (lookupMuValue elid) xi,
                      theta = trilinearInterpolate (lookupThetaValue elid) xi }

        rcCoords : ElementID -> Surface -> RefinedNodeID -> Coord3D
        rcCoords elID surf rnID = prolateToCartesian (rawLookup rawData.distributions 0).averages.flength
                                                         (prolateCoords elID surf rnID)
        elementPrims elID surf =
          let
             narray = fromList (map (rcCoords elID surf) allRefinedNodes)
             nodeAt x y = rawLookup narray (y * refineX + x)
          in
            concatMap (\xlow ->
              concatMap (\ylow ->
                [Triangle (nodeAt xlow ylow) (nodeAt xlow (ylow + 1))
                          (nodeAt (xlow + 1) ylow),
                 Triangle (nodeAt (xlow + 1) ylow) (nodeAt xlow (ylow + 1))
                          (nodeAt (xlow + 1) (ylow + 1))]
              ) [0..(refineY - 2)]
            ) [0..(refineX - 2)]
      in
       GLPrimModel { primitives =
                       concatMap (\surf -> concatMap (\elID -> elementPrims elID surf) showElems)
                                 allSurfaces }

baseModel : Signal GLPrimModel
baseModel = lvJSONToModel allElements <~ lvJSON

main : Signal Element
main =
  pureMain <~ baseModel ~ cameraMatrix ~ cameraMoveState

pureMain baseModelValue cameraMatrixValue cameraMoveStateValue =
    let
      camPerspect = myPerspectiveMatrix `multiply4x4` cameraMatrixValue
      rotatedDiffuseDirection = vec4ToXYZ <| (mat4ToInverseMat3 cameraMatrixValue) `mat4x4xv` initialDiffuseDirection
    in
     (glSceneObject canvasWidth canvasHeight baseModelValue
      (GLPrimSceneView { projection = camPerspect,
                         ambientColour = GLColour 1 1 1,
                         diffuseColour = GLColour 1 1 1,
                         ambientIntensity = 0.4,
                         diffuseIntensity = 0.3,
                         diffuseDirection = rotatedDiffuseDirection }))
     `above` ((flow down . map asText) cameraMoveStateValue.debug)

