open System
open System.Diagnostics
open System.Globalization

open System.Windows
open System.Windows.Input
open System.Windows.Media
open System.Windows.Media.Animation

open System.Numerics

open FSharp.Core.Printf

module GravitySucks =
  type V1 = float32
  type V2 = Vector2

  let debug  msg    = Debug.WriteLine msg
  let debugf fmt    = kprintf debug fmt

  let now           =
    let sw = Stopwatch.StartNew ()
    fun () -> sw.ElapsedMilliseconds

  let inline v1 x   = float32 x
  let inline v2 x y = V2 (float32 x, float32 y)
  let v2_0          = v2 0.F 0.F

  type Particle =
    {
      Mass              : V1
      SqrtMass          : V1
      InvertedMass      : V1
      mutable Current   : V2
      mutable Previous  : V2
    }

    member x.Step (gravity : V1) =
      if x.InvertedMass > 0.0F then
        let c = x.Current
        let d = -c
        let l = d.Length ()
        let g = d*gravity/(l*l*l)
        x.Current   <- g + c + (c - x.Previous)
        x.Previous  <- c
    member x.Speed 
      with get ()         = x.Current - x.Previous
      and  set (spd : V2) = x.Previous <- x.Current - spd
    member x.Translate off =
      x.Current   <- x.Current + off
      x.Previous  <- x.Previous + off

  type Constraint =
    {
      IsStick         : bool
      Length          : V1
      Left            : Particle
      Right           : Particle
    }

    member x.Relax () =
      let l  = x.Left
      let r  = x.Right
      let lc = l.Current
      let rc = r.Current

      let diff  = lc - rc
      let len   = diff.Length ()
      let ldiff = len - x.Length
      let test  = if x.IsStick then abs ldiff > 0.F else ldiff > 0.F
      if test then
        let imass = 0.5F/(l.InvertedMass + r.InvertedMass)
        let mdiff = (imass*ldiff/len)*diff
        let loff  = l.InvertedMass * mdiff
        let roff  = r.InvertedMass * mdiff

        l.Current <- lc - loff
        r.Current <- rc + roff

  type Rocket =
    {
      ConnectedTo : Particle
      AnchoredTo  : Particle
      Force       : V1
      ForwardWhen : Key       array
      ReverseWhen : Key       array
    }

    member x.ForceVector key =
      match key with
      | ValueNone   -> v2_0
      | ValueSome key ->
        let d = V2.Normalize (x.ConnectedTo.Current - x.AnchoredTo.Current)
        let n = v2 d.Y -d.X
        let f = x.Force*n
        if Array.contains key x.ForwardWhen then
          f
        elif Array.contains key x.ReverseWhen then
          -f
        else
          v2_0

  type ParticleSystem =
    {
      Gravity                     : V1
      InnerRadius                 : V1
      Particles                   : Particle    array
      Constraints                 : Constraint  array
      Rockets                     : Rocket      array
      mutable DynamicConstraints  : Constraint  array
    }

    member x.Step key =
      let g = x.Gravity
      // Apply rocket force (if any)
      for r in x.Rockets do
        let f = r.ForceVector key
        let p = r.ConnectedTo
        p.Current <- p.Current + f
      // Step particles to next position
      for p in x.Particles do p.Step g
      // Relax constraints
      for i = 0 to 4 do
        for c in x.Constraints        do c.Relax ()
        for c in x.DynamicConstraints do c.Relax ()
      // Check collision with sun
      let mutable collision = false
      for p in x.Particles do
        let c = p.Current
        let l = c.Length ()
        if l < x.InnerRadius then
          p.Current <- (x.InnerRadius/l)*c
          collision <- true
      collision

  let inline mkParticle mass x y vx vy : Particle =
    let m = v1 mass
    let c = v2 x y
    let v = v2 vx vy
    {
      Mass          = m
      InvertedMass  = 1.0F/m
      SqrtMass      = sqrt m
      Current       = c
      Previous      = c - v
    }

  let inline mkFixParticle x y = mkParticle infinityf x y 0.F 0.F

  let inline mkStick (l : Particle) (r : Particle) : Constraint =
    {
      IsStick   = true
      Length    = (l.Current - r.Current).Length ()
      Left      = l
      Right     = r
    }

  let inline mkRope extraLength (l : Particle) (r : Particle) : Constraint =
    {
      IsStick   = false
      Length    = (1.0F + abs (float32 extraLength))*(l.Current - r.Current).Length ()
      Left      = l
      Right     = r
    }

  let mkRocket 
    connectedTo 
    anchoredTo 
    force 
    forwardWhen 
    reverseWhen   : Rocket =
    {
      ConnectedTo = connectedTo
      AnchoredTo  = anchoredTo 
      Force       = force      
      ForwardWhen = forwardWhen
      ReverseWhen = reverseWhen
    }

  let mkBox mass size x y vx vy : Particle array* Constraint array =
    let inline p x y = mkParticle (0.25F*mass) x y vx vy
    let hsz = 0.5F*size
    let p00 = p (x - hsz) (y - hsz)
    let p01 = p (x - hsz) (y + hsz)
    let p10 = p (x + hsz) (y - hsz)
    let p11 = p (x + hsz) (y + hsz)
    let ps = [|p00; p01; p11; p10|]
    let inline stick i j = mkStick ps.[i] ps.[j]
    let cs =
      [|
        stick 0 1
        stick 1 2
        stick 2 3
        stick 3 0
        stick 0 2
        stick 1 3
      |]
    ps, cs

  let mkTriangle mass size x y vx vy : Particle array* Constraint array =
    let inline p x y = mkParticle (mass/3.0F) x y vx vy
    let xo = size*0.5F
    let yo = size*0.5F/sqrt 3.0F
    let r  = size*1.0F/sqrt 3.0F
    let p0 = p (x - xo) (y - yo)
    let p1 = p (x + xo) (y - yo)
    let p2 = p (x     ) (y + r )
    let ps = [|p0; p1; p2|]
    let inline stick i j = mkStick ps.[i] ps.[j]
    let cs =
      [|
        stick 0 1
        stick 1 2
        stick 2 0
      |]
    ps, cs

  let mkChain constraintFactory n mass b e : Particle array* Constraint array =
    if n < 1 then
      [||], [|constraintFactory b e|]
    else
      let m     = mass/v1 n
      let inline particle (v : V2) = mkParticle m v.X v.Y 0 0
      let diff  = e.Current - b.Current
      let diff  = diff/v1 (n + 1)
      let start = b.Current
      let ps    =
        let initer i = particle (start + v1 (i + 1)*diff)
        Array.init n initer
      let cs    =
        let initer i = constraintFactory ps.[i] ps.[i+1]
        Array.init (n - 1) initer
      let cs    =
        [|
          constraintFactory b ps.[0]
          yield! cs
          constraintFactory e ps.[n-1]
        |]
      ps, cs

  let inline mkSystem 
    gravity           
    innerRadius       
    particles         
    constraints       
    rockets           
    dynamicConstraints  : ParticleSystem =
    {
      Gravity             = gravity           
      InnerRadius         = innerRadius       
      Particles           = particles         
      Constraints         = constraints       
      Rockets             = rockets           
      DynamicConstraints  = dynamicConstraints
    }

  type ConnectorMode =
    | Sticked
    | Roped
    | Fixed

  type RocketMode =
    | JustRight
    | TooMuch
    | Reverse
    | Broken

  type SteeringMode =
    | Normal
    | Top
    | Bottom

  let mkSolarSystem 
    topHeavy 
    extraLongChain 
    connectorMode
    rocketMode
    steeringMode
    bigDelivery       =
    let x , y   = 4.0F, 3.0F
    let coff    = if extraLongChain then 1.0F else 0.5F
    let cx, cy  = x + coff, y + coff
    let dm, dsz = if bigDelivery then 10.0F, 0.25F else 2.0F, 0.125F
    // Ship
    let sps0, scs0  = mkBox       5.0F    0.250F x           y          +0.F      0.F
    let sps1 = [| mkParticle 2.0F (x - 0.25F) (y - 0.25F) 0.0F 0.0F |]
    let scs1 = [| mkStick sps0.[1] sps1.[0]; mkStick sps0.[3] sps1.[0] |]
    // Connector
    let cps0, ccs0  = mkTriangle  1.0F    0.125F  cx     cy     +0.F      0.F
    // Starbase Alpha
    let aps0, acs0  = mkBox       100.0F  0.500F  0.0F  +2.0F   +0.0075F  0.F
    // Starbase Beta
    let bps0, bcs0  = mkBox       100.0F  0.500F  0.0F  -3.25F  -0.0065F  0.F
    // Delivery
    let dps0, dcs0  = mkBox       dm      dsz     0.5F  -3.0F   -0.0065F  0.F

    let lps0, lcs0  = 
      match connectorMode with
      | Sticked ->
        [||], [|mkStick sps0.[2] cps0.[0]|]
      | Roped   ->
        // Chain between ship and connector
        mkChain (mkRope 0.0F) 3 0.5F sps0.[2]  cps0.[0]
      | Fixed ->
        [||], [|mkStick sps0.[3] cps0.[0];mkStick sps0.[1] cps0.[0]|]
    let ps =
      [|
        yield! sps0
        if topHeavy then yield! sps1
        yield! cps0
        yield! aps0
        yield! bps0
        yield! dps0
        yield! lps0
      |]

    let cs =
      [|
        yield! scs0
        if topHeavy then yield! scs1
        yield! ccs0
        yield! acs0
        yield! bcs0
        yield! dcs0
        yield! lcs0
      |]
    let dcs =
      [|
        mkRope 0.5F bps0.[2]  dps0.[0]
      |]
    let bf      = -0.001F
    let lf, rf  =
      match rocketMode with
      | JustRight -> +bf  , -bf
      | Reverse   -> -bf  , +bf
      | Broken    -> +bf  , -0.5F*bf
      | TooMuch   -> let bf = 10.0F*bf in bf, -bf
    let rs =
      match steeringMode with
      | Normal ->
        [|
          mkRocket sps0.[1] sps0.[3] lf [|Key.Up;Key.Right|] [|Key.Down;Key.Left|]
          mkRocket sps0.[3] sps0.[1] rf [|Key.Up;Key.Left|]  [|Key.Down;Key.Right|]
        |]
      | Top ->
        [|
          mkRocket sps0.[1] sps0.[3] lf         [|Key.Up|]    [|Key.Down|]
          mkRocket sps0.[3] sps0.[1] rf         [|Key.Up|]    [|Key.Down|]
          mkRocket sps0.[0] sps0.[2] (1.5F*rf)  [|Key.Left|]  [|Key.Right|]
        |]
      | Bottom ->
        [|
          mkRocket sps0.[1] sps0.[3] lf         [|Key.Up|]    [|Key.Down|]
          mkRocket sps0.[3] sps0.[1] rf         [|Key.Up|]    [|Key.Down|]
          mkRocket sps0.[2] sps0.[0] (1.5F*rf)  [|Key.Left|]  [|Key.Right|]
        |]
    mkSystem 0.000125F 0.4F ps cs rs dcs, cps0, aps0, bps0, dps0

  module Details =
    module Loops =
      let rec avgPosAndSpeed (p : V2) (s : V2) n i (ps : Particle array) =
        if i < ps.Length then
          let pp = ps.[i]
          avgPosAndSpeed (p + pp.Current) (s + pp.Speed) (n + 1) (i + 1) ps
        else
          let f = ((1.0F)/float32 n)
          struct (f*p, f*s)
  open Details

  let avgPosAndSpeed (ps : Particle array) =
    Loops.avgPosAndSpeed ps.[0].Current ps.[0].Speed 1 1 ps

  type GameState =
    | Reset
    | PickingUp
    | Delivering
    | Delivered   of int64

  type Game () =
    class
      let topHeavy          = false
      let extraLongChain    = false
      let connectorMode     = Sticked
      let rocketMode        = JustRight
      let steeringMode      = Bottom
      let bigDelivery       = false

      let particleSystem, connector, alpha, beta, delivery = 
        mkSolarSystem 
          topHeavy 
          extraLongChain
          connectorMode
          rocketMode
          steeringMode
          bigDelivery

      let mutable state = Reset

      member x.Step key =
        let collision = particleSystem.Step key

        match state with
        | Reset     ->
          let struct (betaPos     , betaSpeed)      = avgPosAndSpeed beta
          let struct (deliveryPos , deliverySpeed)  = avgPosAndSpeed delivery

          let t = betaPos - deliveryPos
          for p in delivery do 
            p.Translate t
            p.Speed <- betaSpeed + v2 0.01 0.00

          particleSystem.DynamicConstraints <- 
            [|
              mkRope 0.5F beta.[2] delivery.[0]
            |]

          state <- PickingUp

          ()
        | PickingUp ->
          let struct (connectorPos, connectorSpeed) = avgPosAndSpeed connector
          let struct (deliveryPos , deliverySpeed)  = avgPosAndSpeed delivery

          let posTolerance    = 0.1F
          let speedTolerance  = 1E6F

          let dpos = (connectorPos    - deliveryPos   ).Length ()
          let dspd = (connectorSpeed  - deliverySpeed ).Length ()

          if dpos < posTolerance && dspd < speedTolerance then
            state <- Delivering
            particleSystem.DynamicConstraints <- 
              [|
                mkRope 0.0F connector.[1] delivery.[0]
                mkRope 0.0F connector.[2] delivery.[1]
              |]
          ()
        | Delivering ->
          let struct (alphaPos    , alphaSpeed)     = avgPosAndSpeed alpha
          let struct (deliveryPos , deliverySpeed)  = avgPosAndSpeed delivery

          let posTolerance    = 0.25F
          let speedTolerance  = 1E6F

          let dpos = (alphaPos    - deliveryPos   ).Length ()
          let dspd = (alphaSpeed  - deliverySpeed ).Length ()

          if dpos < posTolerance && dspd < speedTolerance then
            particleSystem.DynamicConstraints <- 
              [|
                mkRope 0.0F alpha.[2] delivery.[0]
              |]
            state <- Delivered (now () + 3000L)
        | Delivered until ->
          if now () < until then
            ()
          else
            state <- Reset

      member x.ParticleSystem = particleSystem

    end

  type GameElement () =
    class
      inherit UIElement ()

      static let timeProperty =
        let pc = PropertyChangedCallback GameElement.TimePropertyChanged
        let md = PropertyMetadata (0.0, pc)
        DependencyProperty.Register ("Time", typeof<float>, typeof<GameElement>, md)

      static let mkPen thickness brush =
        let p = Pen ()
        p.Thickness <- thickness
        p.Brush     <- brush
        p

      let setScale, transform =
        let st  = ScaleTransform (1.0, 1.0)
        let f zoom (sz : Size)=
          let s = 0.5*sz.Height*zoom
          let r = sz.Width/sz.Height
          st.ScaleX   <- s
          st.ScaleY   <- s
          st.CenterX  <- -r/zoom
          st.CenterY  <- -1.0/zoom
          1.0/s
        f, st

      let mutable game = Game ()

      let mutable pressed = ValueNone

      let setThickness, particlePen, stickPen, ropePen, forcePen =
        let p = mkPen 1.0 Brushes.White
        let s = mkPen 1.0 Brushes.Yellow
        let r = mkPen 1.0 Brushes.GreenYellow
        let f = mkPen 1.0 Brushes.Red
        let st pix =
          p.Thickness <- pix
          s.Thickness <- pix
          r.Thickness <- pix
          f.Thickness <- pix
        st, p, s, r, f

      static member TimePropertyChanged (d : DependencyObject) (e : DependencyPropertyChangedEventArgs) =
        let g = d :?> GameElement
        g.InvalidateVisual ()

      static member TimeProperty = timeProperty

      member x.SetupTransform () =
        let rs    = x.RenderSize
        setScale x.Zoom rs

      member val Zoom = 0.25 with get, set

      member x.Time = x.GetValue(GameElement.TimeProperty) :?> float

      member x.Start () =
        let b   = 0.0
        let e   = 1E6
        let dur = Duration (TimeSpan.FromSeconds (e - b))
        let ani = DoubleAnimation (b, e, dur)
        ani.Freeze()
        x.BeginAnimation (GameElement.TimeProperty, ani);

      override x.OnKeyDown e =
        pressed <- ValueSome e.Key

      override x.OnKeyUp e =
        pressed <- ValueNone
        if e.Key = Key.R then
          game <- Game ()

      override x.OnRender dc =
        let inline mkPoint (v2 : V2) = Point (float v2.X, float v2.Y)

        let zoom        = x.Zoom
        let time        = x.Time
        let pix         = x.SetupTransform ()

        setThickness (2.0*pix)

        game.Step pressed
        let particleSystem = game.ParticleSystem

        dc.PushTransform transform

        dc.DrawEllipse(Brushes.Yellow, null, Point(), float particleSystem.InnerRadius, float particleSystem.InnerRadius)

        let inline drawConstraint (c : Constraint) =
          let lc = c.Left.Current
          let rc = c.Right.Current
          let lpt  = mkPoint lc
          let rpt  = mkPoint rc
          let pen  = if c.IsStick then stickPen else ropePen
          dc.DrawLine (pen, lpt, rpt)
        for c in particleSystem.Constraints do
          drawConstraint c
        for c in particleSystem.DynamicConstraints do
          drawConstraint c

        for p in particleSystem.Particles do
          let c   = p.Current
          let psz = zoom*pix*(if p.InvertedMass > 0.0F then (float p.SqrtMass)*10.0 else 10.0)
          let pt  = mkPoint c
          let pen = particlePen
          dc.DrawEllipse (Brushes.Black, pen, pt, psz, psz)

        for r in particleSystem.Rockets do
          let cto = r.ConnectedTo
          let c   = cto.Current
          let f   = -100.0F*r.ForceVector pressed
          let pt0 = mkPoint c
          let pt1 = mkPoint (c + f)
          let pen = forcePen
          dc.DrawLine (pen, pt0, pt1)

        dc.Pop ()

    end

[<EntryPoint>]
[<STAThread>]
let main argv =
  let window  = Window( Title       = "Gravity Sucks!"
                      , Background  = Brushes.Black
                      )
  let element = GravitySucks.GameElement ()
  window.Content    <- element
  element.Focusable <- true
  element.Focus () |> ignore
  element.Start ()
  window.ShowDialog () |> ignore
  0
