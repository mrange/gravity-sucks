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

    member x.Step (g : V1) =
      if x.InvertedMass > 0.0F then
        let c = x.Current
        let d = -c
        let l = d.Length ()
        let n = d/l
        let g = n/(l*l)*g
        x.Current   <- g + c + (c - x.Previous)
        x.Previous  <- c
    member x.Speed = x.Current - x.Previous

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

    member x.ForceVector k =
      match k with
      | ValueNone   -> v2_0
      | ValueSome k ->
        let d = V2.Normalize (x.ConnectedTo.Current - x.AnchoredTo.Current)
        let n = v2 d.Y -d.X
        let f = x.Force*n
        if Array.contains k x.ForwardWhen then
          f
        elif Array.contains k x.ReverseWhen then
          -f
        else
          v2_0

  type ParticleSystem =
    {
      InnerRadius                 : V1
      Particles                   : Particle    array
      Constraints                 : Constraint  array
      Rockets                     : Rocket      array
      mutable DynamicConstraints  : Constraint  array
    }

    member x.Step g k =
      for r in x.Rockets do
        let f = r.ForceVector k
        let p = r.ConnectedTo
        p.Current <- p.Current - f
      for p in x.Particles do p.Step g
      for i = 0 to 4 do
        for c in x.Constraints        do c.Relax ()
        for c in x.DynamicConstraints do c.Relax ()
      for p in x.Particles do
        let c = p.Current
        let l = c.Length ()
        if l < x.InnerRadius then
          p.Current <- (x.InnerRadius/l)*c

  let inline mkParticle m x y vx vy : Particle =
    let m = v1 m
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

  let inline mkConstraint s (l : Particle) (r : Particle) : Constraint =
    {
      IsStick   = s
      Length    = (l.Current - r.Current).Length ()
      Left      = l
      Right     = r
    }

  let mkRocket cto ato f fw rw : Rocket =
    {
      ConnectedTo = cto
      AnchoredTo  = ato
      Force       = f
      ForwardWhen = fw
      ReverseWhen = rw
    }

  let mkBox m sz x y vx vy : Particle array* Constraint array =
    let inline p x y = mkParticle (0.25F*m) x y vx vy
    let hsz = 0.5F*sz
    let p00 = p (x - hsz) (y - hsz)
    let p01 = p (x - hsz) (y + hsz)
    let p10 = p (x + hsz) (y - hsz)
    let p11 = p (x + hsz) (y + hsz)
    let ps = [|p00; p01; p11; p10|]
    let inline stick i j = mkConstraint true   ps[i] ps[j]
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

  let mkTriangle m sz x y vx vy : Particle array* Constraint array =
    let inline p x y = mkParticle (0.25F*m) x y vx vy
    let xo = sz*0.5F
    let yo = sz*0.5F/sqrt 3.0F
    let r  = sz*1.0F/sqrt 3.0F
    let p0 = p (x - xo) (y - yo)
    let p1 = p (x + xo) (y - yo)
    let p2 = p (x     ) (y + r )
    let ps = [|p0; p1; p2|]
    let inline stick i j = mkConstraint true   ps[i] ps[j]
    let cs =
      [|
        stick 0 1
        stick 1 2
        stick 2 0
      |]
    ps, cs

  let mkChain n m f s : Particle array* Constraint array =
    let inline rope f s = mkConstraint false f s
    if n < 1 then
      [||], [|rope f s|]
    else
      let m     = m/v1 n
      let inline particle (v : V2) = mkParticle m v.X v.Y 0 0
      let diff  = s.Current - f.Current
      let diff  = diff/v1 (n + 1)
      let start = f.Current
      let ps    =
        let initer i = particle (start + v1 (i + 1)*diff)
        Array.init n initer
      let cs    =
        let initer i = rope ps[i] ps[i+1]
        Array.init (n - 1) initer
      let cs    =
        [|
          rope f ps[0]
          yield! cs
          rope s ps[n-1]
        |]
      ps, cs


  let inline mkSystem ps cs dcs rs : ParticleSystem =
    {
      InnerRadius         = 0.5F
      Particles           = ps
      Constraints         = cs
      Rockets             = rs
      DynamicConstraints  = dcs
    }

  let mkSolarSystem () =
    let x, y        = 4.0F, 3.0F
    // Ship
    let bps0, bcs0  = mkBox       5.0F    0.250F x           y          0.F       0.F
    // Connector
    let bps1, bcs1  = mkTriangle  1.0F    0.125F (x + 0.5F)  (y + 0.5F) 0.F       0.F
    // Starbase #0
    let bps2, bcs2  = mkBox       100.0F  0.500F 0.0F        +2.0F      +0.0075F  0.F
    // Starbase #1
    let bps3, bcs3  = mkBox       100.0F  0.500F 0.0F        -3.0F      -0.0065F  0.F
    // Shipment
    let bps4, bcs4  = mkBox       2.0F    0.125F 0.5F        -3.0F      -0.0065F  0.F

    // Chain between ship and connector
    let cps0, ccs0  = mkChain 3 0.5F bps0[2]  bps1[0]
    let ps =
      [|
        yield! bps0
        yield! bps1
        yield! bps2
        yield! bps3
        yield! bps4
        yield! cps0
      |]

    let cs =
      [|
        yield! bcs0
        yield! bcs1
        yield! bcs2
        yield! bcs3
        yield! bcs4
        yield! ccs0
      |]
    let dcs =
      [|
        mkConstraint false bps3[2]  bps4[0]
      |]
    let f = 0.001F
    let rs =
      [|
        mkRocket bps0[1] bps0[3] +f [|Key.Up;Key.Right|] [|Key.Down;Key.Left|]
        mkRocket bps0[3] bps0[1] -f [|Key.Up;Key.Left|]  [|Key.Down;Key.Right|]
      |]
    mkSystem ps cs dcs rs, bps1, bps2, bps3, bps4

  module Details =
    module Loops =
      let rec avgPosAndSpeed (p : V2) (s : V2) n i (ps : Particle array) =
        if i < ps.Length then
          let pp = ps[i]
          avgPosAndSpeed (p + pp.Current) (s + pp.Speed) (n + 1) (i + 1) ps
        else
          let f = ((1.0F)/float32 n)
          struct (f*p, f*s)
  open Details

  let rec avgPosAndSpeed (ps : Particle array) =
    Loops.avgPosAndSpeed ps[0].Current ps[0].Speed 1 1 ps

  type GameState =
    | PickingUp
    | Delivering
    | Done
  type Game () =
    class
      let gravity = 0.000125F

      let particleSystem, connector, base0, base1, shipment = mkSolarSystem ()

      let mutable state = PickingUp

      member x.Step k =
        particleSystem.Step gravity k

        match state with
        | PickingUp ->
          let struct (connectorPos, connectorSpeed) = avgPosAndSpeed connector
          let struct (shipmentPos , shipmentSpeed)  = avgPosAndSpeed shipment

          let posTolerance    = 0.1F
          let speedTolerance  = 1E6F

          let dpos = (connectorPos    - shipmentPos   ).Length ()
          let dspd = (connectorSpeed  - shipmentSpeed ).Length ()

//          debugf "%f, %f" dpos dspd

          if dpos < posTolerance && dspd < speedTolerance then
            state <- Delivering
            particleSystem.DynamicConstraints <- 
              [|
                mkConstraint false connector[1] shipment[0]
                mkConstraint false connector[2] shipment[1]
              |]
          ()
        | Delivering ->
          let struct (base0Pos    , base0Speed)     = avgPosAndSpeed base0
          let struct (shipmentPos , shipmentSpeed)  = avgPosAndSpeed shipment

          let posTolerance    = 0.25F
          let speedTolerance  = 1E6F

          let dpos = (base0Pos    - shipmentPos   ).Length ()
          let dspd = (base0Speed  - shipmentSpeed ).Length ()

          if dpos < posTolerance && dspd < speedTolerance then
            state <- Done
            particleSystem.DynamicConstraints <- Array.empty
          ()
        | Done ->
          ()



        ()

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

      let game = Game ()

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
          let f   = 100.0F*r.ForceVector pressed
          let pt0 = mkPoint c
          let pt1 = mkPoint (c + f)
          let pen = forcePen
          dc.DrawLine (pen, pt0, pt1)

        dc.Pop ()

    end

[<EntryPoint>]
[<STAThread>]
let main argv =
  let window  = Window( Title = "Gravity Sucks!"
                      , Background = Brushes.Black
                      )
  let element = GravitySucks.GameElement ()
  window.Content    <- element
  element.Focusable <- true
  element.Focus () |> ignore
  element.Start ()
  window.ShowDialog () |> ignore
  0
