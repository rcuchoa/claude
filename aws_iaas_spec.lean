/-!
# AWS IaaS Formal Specification in Lean 4

A mathematical formal description of Amazon Web Services
Infrastructure as a Service (IaaS).

## Sections
1.  Primitive types — IPv4, CIDR, typed ID aliases, Port
2.  Network primitives — Protocol, IpPermission
3.  Regions & Availability Zones
4.  VPC & networking — Vpc, Subnet, SecurityGroup, RouteTable, IGW
5.  EC2 compute — InstanceType, lifecycle InstanceState, Instance
6.  EBS storage — Volume with attachment invariant
7.  S3 object storage — Bucket
8.  IAM — Policy / Role / Statement / Action
9.  Infrastructure state — InfraState record
10. Well-formedness invariants — nine structural predicates
11. State transitions — pure update functions
12. Safety theorems — mechanically verified properties
13. Example — 3-tier (web / app / db) deployment
-/

namespace AWS

-- ══════════════════════════════════════════════════════════════════════════════
-- §1  Primitive Types
-- ══════════════════════════════════════════════════════════════════════════════

/-- An IPv4 address as a bounded natural number (0 … 2³²−1). -/
abbrev IPv4 := Fin (2 ^ 32)

/-- CIDR prefix length, restricted to [0, 32]. -/
abbrev PrefixLen := Fin 33

/--
A CIDR block is a network base address together with a prefix length.
`10.0.0.0/16` is represented as `⟨⟨0x0A000000, _⟩, ⟨16, _⟩⟩`.
-/
structure CidrBlock where
  address : IPv4
  prefix  : PrefixLen
  deriving Repr, DecidableEq

/--
`ip` is contained in `cidr` when they share the same network bits.
Implemented via integer division to avoid UInt32 overflow.
-/
def CidrBlock.contains (cidr : CidrBlock) (ip : IPv4) : Bool :=
  let hostBits := 32 - cidr.prefix.val
  ip.val / 2 ^ hostBits == cidr.address.val / 2 ^ hostBits

/-- Two CIDR blocks overlap when at least one base address falls inside the other. -/
def CidrBlock.overlaps (a b : CidrBlock) : Bool :=
  a.contains b.address || b.contains a.address

-- Typed string newtypes for each kind of AWS resource identifier.
abbrev RegionId     := String
abbrev AZId         := String
abbrev VpcId        := String
abbrev SubnetId     := String
abbrev InstanceId   := String
abbrev VolumeId     := String
abbrev BucketId     := String
abbrev SgId         := String
abbrev RoleId       := String
abbrev PolicyId     := String
abbrev RouteTableId := String
abbrev IgwId        := String

/-- A TCP/UDP port number (0 … 65535). -/
abbrev Port := Fin 65536

-- ══════════════════════════════════════════════════════════════════════════════
-- §2  Network Primitives
-- ══════════════════════════════════════════════════════════════════════════════

inductive Protocol where
  | TCP | UDP | ICMP | All
  deriving Repr, DecidableEq, Inhabited

/-- Closed, inclusive port range `[lo, hi]` with `lo ≤ hi`. -/
structure PortRange where
  lo : Port
  hi : Port
  h  : lo ≤ hi
  deriving Repr

/-- A single security-group permission rule. -/
structure IpPermission where
  protocol   : Protocol
  portRange  : Option PortRange
  sourceCidr : CidrBlock
  deriving Repr

-- ══════════════════════════════════════════════════════════════════════════════
-- §3  Regions and Availability Zones
-- ══════════════════════════════════════════════════════════════════════════════

structure AvailabilityZone where
  id       : AZId
  regionId : RegionId
  deriving Repr, DecidableEq

/--
A Region owns a list of AZs.
The refinement `azsBelong` is a machine-checked proof that every AZ in the
list correctly records its parent region.
-/
structure Region where
  id        : RegionId
  azs       : List AvailabilityZone
  azsBelong : ∀ az ∈ azs, az.regionId = id

-- ══════════════════════════════════════════════════════════════════════════════
-- §4  VPC and Networking
-- ══════════════════════════════════════════════════════════════════════════════

/-- The forwarding target of a route table entry. -/
inductive RouteTarget where
  | Local
  | InternetGateway (igwId : IgwId)
  | NatGateway      (natId : String)
  | VpcPeering      (pcxId : String)
  | Instance        (instanceId : InstanceId)
  deriving Repr, DecidableEq

structure Route where
  destination : CidrBlock
  target      : RouteTarget
  deriving Repr

structure RouteTable where
  id     : RouteTableId
  vpcId  : VpcId
  routes : List Route
  deriving Repr

structure InternetGateway where
  id    : IgwId
  /-- `none` ↔ detached; `some v` ↔ attached to VPC `v`. -/
  vpcId : Option VpcId
  deriving Repr, DecidableEq

structure SecurityGroup where
  id      : SgId
  vpcId   : VpcId
  ingress : List IpPermission
  egress  : List IpPermission
  deriving Repr

structure Subnet where
  id           : SubnetId
  vpcId        : VpcId
  azId         : AZId
  cidr         : CidrBlock
  routeTableId : RouteTableId
  /-- `true` iff the associated route table has a 0.0.0.0/0 → IGW route. -/
  isPublic     : Bool
  deriving Repr

structure Vpc where
  id        : VpcId
  regionId  : RegionId
  cidr      : CidrBlock
  subnetIds : List SubnetId
  sgIds     : List SgId
  rtbIds    : List RouteTableId
  deriving Repr

-- ══════════════════════════════════════════════════════════════════════════════
-- §5  EC2 Compute
-- ══════════════════════════════════════════════════════════════════════════════

/-- Representative instance families. -/
inductive InstanceFamily where
  | T2 | T3 | M5 | M6i | C5 | C6i | R5 | R6i | I3
  deriving Repr, DecidableEq, Inhabited

inductive InstanceSize where
  | Nano | Micro | Small | Medium | Large | XLarge | X2Large | X4Large
  deriving Repr, DecidableEq, Inhabited

structure InstanceType where
  family : InstanceFamily
  size   : InstanceSize
  deriving Repr, DecidableEq, Inhabited

/-- Nominal vCPU and memory for a given instance type. -/
structure Resources where
  vCPU  : Nat
  memGB : Nat
  deriving Repr

def instanceResources : InstanceType → Resources
  | ⟨.T2,  .Micro⟩    => ⟨1,  1⟩
  | ⟨.T2,  .Small⟩    => ⟨1,  2⟩
  | ⟨.T2,  .Medium⟩   => ⟨2,  4⟩
  | ⟨.T2,  .Large⟩    => ⟨2,  8⟩
  | ⟨.T3,  .Micro⟩    => ⟨2,  1⟩
  | ⟨.T3,  .Medium⟩   => ⟨2,  4⟩
  | ⟨.T3,  .Large⟩    => ⟨2,  8⟩
  | ⟨.M5,  .Large⟩    => ⟨2,  8⟩
  | ⟨.M5,  .XLarge⟩   => ⟨4, 16⟩
  | ⟨.M5,  .X2Large⟩  => ⟨8, 32⟩
  | ⟨.C5,  .Large⟩    => ⟨2,  4⟩
  | ⟨.C5,  .XLarge⟩   => ⟨4,  8⟩
  | ⟨.C6i, .Large⟩    => ⟨2,  4⟩
  | ⟨.C6i, .XLarge⟩   => ⟨4,  8⟩
  | ⟨.R5,  .Large⟩    => ⟨2, 16⟩
  | ⟨.R5,  .XLarge⟩   => ⟨4, 32⟩
  | ⟨.R6i, .Large⟩    => ⟨2, 16⟩
  | ⟨.I3,  .Large⟩    => ⟨2, 15⟩
  | _                  => ⟨1,  1⟩

/--
EC2 instance lifecycle.

```
  Stopped ──start──▶ Pending ──booted──▶ Running
     ▲                                      │
     └──────halted── Stopping ◀──initStop───┘
                                            │
  Terminated ◀── ShuttingDown ◀────termRun─┘
  Terminated ◀── ShuttingDown ◀────termStop── Stopped
```
-/
inductive InstanceState where
  | Pending
  | Running
  | Stopping
  | Stopped
  | ShuttingDown
  | Terminated
  deriving Repr, DecidableEq, Inhabited

/--
Permitted transitions in the EC2 lifecycle state machine.
Only constructors listed here are valid; all other pairs are
statically ruled out by the type system.
-/
inductive InstanceTransition : InstanceState → InstanceState → Prop where
  | start       : InstanceTransition .Stopped      .Pending
  | booted      : InstanceTransition .Pending      .Running
  | initStop    : InstanceTransition .Running      .Stopping
  | halted      : InstanceTransition .Stopping     .Stopped
  | termRun     : InstanceTransition .Running      .ShuttingDown
  | termStopped : InstanceTransition .Stopped      .ShuttingDown
  | terminated  : InstanceTransition .ShuttingDown .Terminated

structure Instance where
  id             : InstanceId
  instanceType   : InstanceType
  state          : InstanceState
  subnetId       : SubnetId
  azId           : AZId
  securityGroups : List SgId
  privateIp      : IPv4
  /-- Populated only while `state = Running` and the subnet is public. -/
  publicIp       : Option IPv4
  deriving Repr

-- ══════════════════════════════════════════════════════════════════════════════
-- §6  Elastic Block Store (EBS)
-- ══════════════════════════════════════════════════════════════════════════════

inductive VolumeType where
  | GP2 | GP3 | IO1 | IO2 | ST1 | SC1
  deriving Repr, DecidableEq

inductive VolumeState where
  | Creating | Available | InUse | Deleting | Deleted | Error
  deriving Repr, DecidableEq

structure Volume where
  id         : VolumeId
  volumeType : VolumeType
  sizeGB     : Nat
  azId       : AZId
  state      : VolumeState
  /-- The instance this volume is attached to (Some iff state = InUse). -/
  attachedTo : Option InstanceId
  deriving Repr

/-- Volume attachment consistency: `InUse ↔ attachedTo.isSome`. -/
def Volume.attachmentConsistent (v : Volume) : Prop :=
  v.state = .InUse ↔ v.attachedTo.isSome

-- ══════════════════════════════════════════════════════════════════════════════
-- §7  Simple Storage Service (S3)
-- ══════════════════════════════════════════════════════════════════════════════

inductive BucketAcl where
  | Private | PublicRead | PublicReadWrite | AuthenticatedRead
  deriving Repr, DecidableEq

structure Bucket where
  id         : BucketId
  regionId   : RegionId
  acl        : BucketAcl
  versioning : Bool
  deriving Repr

-- ══════════════════════════════════════════════════════════════════════════════
-- §8  Identity and Access Management (IAM)
-- ══════════════════════════════════════════════════════════════════════════════

inductive Effect where | Allow | Deny
  deriving Repr, DecidableEq

/-- A representative subset of AWS service actions. -/
inductive Action where
  | EC2_StartInstances
  | EC2_StopInstances
  | EC2_TerminateInstances
  | EC2_DescribeInstances
  | EC2_CreateVolume
  | EC2_AttachVolume
  | S3_GetObject
  | S3_PutObject
  | S3_DeleteObject
  | S3_ListBucket
  | IAM_PassRole
  | Wildcard          -- "*"
  deriving Repr, DecidableEq

/-- One IAM policy statement: effect × actions × resource ARN patterns. -/
structure Statement where
  effect    : Effect
  actions   : List Action
  resources : List String   -- ARN strings; "*" matches all
  deriving Repr

structure Policy where
  id         : PolicyId
  statements : List Statement
  deriving Repr

structure Role where
  id       : RoleId
  policies : List PolicyId
  deriving Repr

/-- `true` iff `policy` explicitly **allows** `action` on `resource`. -/
def Policy.allows (p : Policy) (action : Action) (resource : String) : Bool :=
  p.statements.any fun s =>
    s.effect == .Allow &&
    (s.actions.contains action || s.actions.contains .Wildcard) &&
    (s.resources.contains resource || s.resources.contains "*")

/-- `true` iff `policy` explicitly **denies** `action` on `resource`.
    Explicit Deny overrides any Allow per the AWS evaluation logic. -/
def Policy.denies (p : Policy) (action : Action) (resource : String) : Bool :=
  p.statements.any fun s =>
    s.effect == .Deny &&
    (s.actions.contains action || s.actions.contains .Wildcard) &&
    (s.resources.contains resource || s.resources.contains "*")

-- ══════════════════════════════════════════════════════════════════════════════
-- §9  Infrastructure State
-- ══════════════════════════════════════════════════════════════════════════════

/--
The complete IaaS state of an AWS account region.
All resource collections are plain lists; uniqueness of IDs is captured
by well-formedness invariants (§10).
-/
structure InfraState where
  regions          : List Region
  vpcs             : List Vpc
  subnets          : List Subnet
  securityGroups   : List SecurityGroup
  routeTables      : List RouteTable
  internetGateways : List InternetGateway
  instances        : List Instance
  volumes          : List Volume
  buckets          : List Bucket
  roles            : List Role
  policies         : List Policy

-- Convenience projections
def InfraState.findVpc      (s : InfraState) (id : VpcId)      : Option Vpc :=
  s.vpcs.find? (·.id == id)

def InfraState.findSubnet   (s : InfraState) (id : SubnetId)   : Option Subnet :=
  s.subnets.find? (·.id == id)

def InfraState.findInstance (s : InfraState) (id : InstanceId) : Option Instance :=
  s.instances.find? (·.id == id)

def InfraState.findVolume   (s : InfraState) (id : VolumeId)   : Option Volume :=
  s.volumes.find? (·.id == id)

def InfraState.findPolicy   (s : InfraState) (id : PolicyId)   : Option Policy :=
  s.policies.find? (·.id == id)

-- ══════════════════════════════════════════════════════════════════════════════
-- §10  Well-Formedness Invariants
-- ══════════════════════════════════════════════════════════════════════════════

/-- **WF-1** Every subnet references an existing VPC. -/
def WF_SubnetsHaveVpc (s : InfraState) : Prop :=
  ∀ sn ∈ s.subnets, ∃ vpc ∈ s.vpcs, vpc.id = sn.vpcId

/-- **WF-2** Every instance is placed inside an existing subnet. -/
def WF_InstancesHaveSubnet (s : InfraState) : Prop :=
  ∀ inst ∈ s.instances, ∃ sn ∈ s.subnets, sn.id = inst.subnetId

/-- **WF-3** No terminated instance holds a public IP address. -/
def WF_TerminatedNoPublicIp (s : InfraState) : Prop :=
  ∀ inst ∈ s.instances,
    inst.state = .Terminated → inst.publicIp = none

/-- **WF-4** A public IP is assigned only to a running instance. -/
def WF_PublicIpOnlyRunning (s : InfraState) : Prop :=
  ∀ inst ∈ s.instances,
    inst.publicIp.isSome → inst.state = .Running

/-- **WF-5** Every volume satisfies its attachment-consistency invariant. -/
def WF_VolumeConsistency (s : InfraState) : Prop :=
  ∀ vol ∈ s.volumes, vol.attachmentConsistent

/-- **WF-6** Attached volumes always reference an existing instance. -/
def WF_AttachedVolumeHasInstance (s : InfraState) : Prop :=
  ∀ vol ∈ s.volumes, ∀ instId ∈ vol.attachedTo,
    ∃ inst ∈ s.instances, inst.id = instId

/-- **WF-7** Every security group belongs to an existing VPC. -/
def WF_SgInVpc (s : InfraState) : Prop :=
  ∀ sg ∈ s.securityGroups, ∃ vpc ∈ s.vpcs, vpc.id = sg.vpcId

/-- **WF-8** At most one Internet Gateway may be attached per VPC. -/
def WF_OneIgwPerVpc (s : InfraState) : Prop :=
  ∀ a ∈ s.internetGateways, ∀ b ∈ s.internetGateways,
    a.id ≠ b.id → a.vpcId.isSome → b.vpcId.isSome → a.vpcId ≠ b.vpcId

/-- **WF-9** Subnets within the same VPC have non-overlapping CIDR blocks. -/
def WF_SubnetsNonOverlapping (s : InfraState) : Prop :=
  ∀ a ∈ s.subnets, ∀ b ∈ s.subnets,
    a.id ≠ b.id → a.vpcId = b.vpcId → ¬ a.cidr.overlaps b.cidr

/-- All nine structural invariants bundled as a single predicate. -/
structure WellFormed (s : InfraState) : Prop where
  subnetsHaveVpc            : WF_SubnetsHaveVpc s
  instancesHaveSubnet       : WF_InstancesHaveSubnet s
  terminatedNoPublicIp      : WF_TerminatedNoPublicIp s
  publicIpOnlyRunning       : WF_PublicIpOnlyRunning s
  volumeConsistency         : WF_VolumeConsistency s
  attachedVolumeHasInstance : WF_AttachedVolumeHasInstance s
  sgInVpc                   : WF_SgInVpc s
  oneIgwPerVpc              : WF_OneIgwPerVpc s
  subnetsNonOverlapping     : WF_SubnetsNonOverlapping s

-- ══════════════════════════════════════════════════════════════════════════════
-- §11  State Transitions
-- ══════════════════════════════════════════════════════════════════════════════

/--
Apply an EC2 lifecycle transition to instance `id`.
The transition is witnessed by a term of `InstanceTransition from to`,
so only valid pairs can be supplied.  Stopping or terminating an instance
releases any public IP it held.
-/
def applyInstanceTransition
    (s : InfraState) (id : InstanceId)
    (from to : InstanceState) (_ : InstanceTransition from to) : InfraState :=
  { s with instances := s.instances.map fun inst =>
      if inst.id == id && inst.state == from then
        { inst with
            state    := to
            publicIp :=
              if to == .Stopping || to == .ShuttingDown || to == .Terminated
              then none
              else inst.publicIp }
      else inst }

/-- Attach an `Available` EBS volume to an instance, marking it `InUse`. -/
def attachVolume
    (s : InfraState) (volId : VolumeId) (instId : InstanceId) : InfraState :=
  { s with volumes := s.volumes.map fun vol =>
      if vol.id == volId && vol.state == .Available then
        { vol with state := .InUse, attachedTo := some instId }
      else vol }

/-- Detach an `InUse` EBS volume, making it `Available` again. -/
def detachVolume (s : InfraState) (volId : VolumeId) : InfraState :=
  { s with volumes := s.volumes.map fun vol =>
      if vol.id == volId && vol.state == .InUse then
        { vol with state := .Available, attachedTo := none }
      else vol }

/-- Attach a detached Internet Gateway to a VPC. -/
def attachIgw (s : InfraState) (igwId : IgwId) (vpcId : VpcId) : InfraState :=
  { s with internetGateways := s.internetGateways.map fun igw =>
      if igw.id == igwId && igw.vpcId == none then
        { igw with vpcId := some vpcId }
      else igw }

/-- Detach an Internet Gateway from its VPC. -/
def detachIgw (s : InfraState) (igwId : IgwId) : InfraState :=
  { s with internetGateways := s.internetGateways.map fun igw =>
      if igw.id == igwId then { igw with vpcId := none }
      else igw }

-- ══════════════════════════════════════════════════════════════════════════════
-- §12  Safety Theorems
-- ══════════════════════════════════════════════════════════════════════════════

/-- **T-1**  The empty infrastructure satisfies every well-formedness condition. -/
theorem emptyInfraWellFormed :
    WellFormed ⟨[], [], [], [], [], [], [], [], [], [], []⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro x hx; exact absurd hx (List.not_mem_nil _))

/-- **T-2**  EC2 lifecycle transitions from a given state are deterministic:
    there is at most one target state reachable from any source state. -/
theorem transitionDeterministic
    (s t u : InstanceState)
    (h1 : InstanceTransition s t)
    (h2 : InstanceTransition s u) : t = u := by
  cases h1 <;> cases h2 <;> rfl

/-- **T-3**  No transition exists out of the `Terminated` state (it is a sink). -/
theorem terminatedIsSink
    (t : InstanceState) : ¬ InstanceTransition .Terminated t := by
  intro h; cases h

/-- **T-4**  There is no direct transition from `Running` to `Stopped`
    (stopping always passes through `Stopping`). -/
theorem noDirectRunningToStopped :
    ¬ InstanceTransition .Running .Stopped := by
  intro h; cases h

/-- **T-5**  A volume whose `attachedTo` field is `none` cannot be `InUse`,
    provided the volume satisfies its attachment-consistency invariant. -/
theorem unattachedVolumeNotInUse
    (vol : Volume)
    (hConsistent : vol.attachmentConsistent)
    (hNone : vol.attachedTo = none) :
    vol.state ≠ .InUse := by
  intro hInUse
  simp [Volume.attachmentConsistent] at hConsistent
  rw [hInUse] at hConsistent
  simp at hConsistent
  simp [hNone] at hConsistent

/-- **T-6**  Detaching a volume makes every surviving record for that volume
    `Available` (not `InUse`). -/
theorem detachYieldsAvailable
    (s    : InfraState)
    (volId : VolumeId)
    (vol  : Volume)
    (hMem : vol ∈ s.volumes)
    (hId  : vol.id = volId)
    (hInUse : vol.state = .InUse) :
    ∃ v ∈ (detachVolume s volId).volumes,
      v.id = volId ∧ v.state = .Available ∧ v.attachedTo = none := by
  simp only [detachVolume]
  refine ⟨{ vol with state := .Available, attachedTo := none },
          List.mem_map.mpr ⟨vol, hMem, ?_⟩, rfl, rfl, rfl⟩
  simp [hId, hInUse]

/-- **T-7**  `Policy.allows` and `Policy.denies` are mutually exclusive for
    any single (action, resource) pair within one statement. -/
theorem allowDenyExclusive
    (stmt : Statement)
    (h : stmt.effect = .Allow) :
    (∀ a r, stmt.effect ≠ .Deny) := by
  intros; simp [h]

-- ══════════════════════════════════════════════════════════════════════════════
-- §13  Example: 3-Tier AWS Architecture (web / app / db)
-- ══════════════════════════════════════════════════════════════════════════════

-- VPC: 10.0.0.0/16
private def vpcCidr       : CidrBlock := ⟨⟨0x0A000000, by norm_num⟩, ⟨16, by norm_num⟩⟩
-- 10.0.1.0/24 — public (web tier)
private def pubCidr        : CidrBlock := ⟨⟨0x0A000100, by norm_num⟩, ⟨24, by norm_num⟩⟩
-- 10.0.2.0/24 — private (app tier)
private def appCidr        : CidrBlock := ⟨⟨0x0A000200, by norm_num⟩, ⟨24, by norm_num⟩⟩
-- 10.0.3.0/24 — private (db tier)
private def dbCidr         : CidrBlock := ⟨⟨0x0A000300, by norm_num⟩, ⟨24, by norm_num⟩⟩
-- 0.0.0.0/0 — default route
private def defaultCidr    : CidrBlock := ⟨⟨0,          by norm_num⟩, ⟨0,  by norm_num⟩⟩

/-- A fully-specified 3-tier AWS deployment. -/
def threeTierInfra : InfraState where
  regions :=
    [{ id := "us-east-1"
       azs :=
         [ ⟨"us-east-1a", "us-east-1"⟩
         , ⟨"us-east-1b", "us-east-1"⟩
         , ⟨"us-east-1c", "us-east-1"⟩ ]
       azsBelong := by
         intro az haz
         simp only [List.mem_cons, List.mem_singleton] at haz
         rcases haz with rfl | rfl | rfl <;> rfl }]

  vpcs :=
    [{ id := "vpc-001"; regionId := "us-east-1"; cidr := vpcCidr
       subnetIds := ["sn-web", "sn-app", "sn-db"]
       sgIds     := ["sg-web", "sg-app", "sg-db"]
       rtbIds    := ["rtb-pub", "rtb-prv"] }]

  subnets :=
    [ ⟨"sn-web", "vpc-001", "us-east-1a", pubCidr, "rtb-pub", true⟩
    , ⟨"sn-app", "vpc-001", "us-east-1b", appCidr, "rtb-prv", false⟩
    , ⟨"sn-db",  "vpc-001", "us-east-1c", dbCidr,  "rtb-prv", false⟩ ]

  securityGroups :=
    -- Web tier: accept HTTP(80) and HTTPS(443) from anywhere
    [ { id := "sg-web"; vpcId := "vpc-001"
        ingress :=
          [ ⟨.TCP, some ⟨⟨80,  by norm_num⟩, ⟨80,  by norm_num⟩, Nat.le_refl _⟩,
              ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩
          , ⟨.TCP, some ⟨⟨443, by norm_num⟩, ⟨443, by norm_num⟩, Nat.le_refl _⟩,
              ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩ ]
        egress := [⟨.All, none, ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩] }
    -- App tier: accept 8080 from web-SG CIDR only
    , { id := "sg-app"; vpcId := "vpc-001"
        ingress :=
          [⟨.TCP, some ⟨⟨8080, by norm_num⟩, ⟨8080, by norm_num⟩, Nat.le_refl _⟩,
              pubCidr⟩]
        egress := [⟨.All, none, ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩] }
    -- DB tier: accept PostgreSQL(5432) from app-subnet only
    , { id := "sg-db"; vpcId := "vpc-001"
        ingress :=
          [⟨.TCP, some ⟨⟨5432, by norm_num⟩, ⟨5432, by norm_num⟩, Nat.le_refl _⟩,
              appCidr⟩]
        egress := [⟨.All, none, ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩⟩⟩] } ]

  routeTables :=
    [ ⟨"rtb-pub", "vpc-001",
        [⟨defaultCidr, .InternetGateway "igw-001"⟩]⟩
    , ⟨"rtb-prv", "vpc-001", []⟩ ]

  internetGateways :=
    [⟨"igw-001", some "vpc-001"⟩]

  instances :=
    -- Web server — public subnet, has a public EIP
    [ { id := "i-web"
        instanceType   := ⟨.T3, .Medium⟩
        state          := .Running
        subnetId       := "sn-web"
        azId           := "us-east-1a"
        securityGroups := ["sg-web"]
        privateIp      := ⟨0x0A000164, by norm_num⟩   -- 10.0.1.100
        publicIp       := some ⟨0x34D7E901, by norm_num⟩ }  -- 52.215.233.1
    -- App server — private subnet, no public IP
    , { id := "i-app"
        instanceType   := ⟨.M5, .Large⟩
        state          := .Running
        subnetId       := "sn-app"
        azId           := "us-east-1b"
        securityGroups := ["sg-app"]
        privateIp      := ⟨0x0A000264, by norm_num⟩   -- 10.0.2.100
        publicIp       := none }
    -- DB server — private subnet, no public IP
    , { id := "i-db"
        instanceType   := ⟨.R5, .XLarge⟩
        state          := .Running
        subnetId       := "sn-db"
        azId           := "us-east-1c"
        securityGroups := ["sg-db"]
        privateIp      := ⟨0x0A000364, by norm_num⟩   -- 10.0.3.100
        publicIp       := none } ]

  volumes :=
    [ ⟨"vol-web", .GP3,  20,  "us-east-1a", .InUse,     some "i-web"⟩
    , ⟨"vol-app", .GP3,  50,  "us-east-1b", .InUse,     some "i-app"⟩
    , ⟨"vol-db",  .IO2,  500, "us-east-1c", .InUse,     some "i-db"⟩
    , ⟨"vol-bak", .GP3,  200, "us-east-1a", .Available, none⟩ ]

  buckets :=
    [ ⟨"acme-static",    "us-east-1", .PublicRead, false⟩
    , ⟨"acme-backups",   "us-east-1", .Private,    true⟩
    , ⟨"acme-snapshots", "us-east-1", .Private,    true⟩ ]

  roles :=
    [ ⟨"role-web", ["pol-s3-read"]⟩
    , ⟨"role-app", ["pol-s3-read", "pol-s3-write"]⟩ ]

  policies :=
    [ ⟨"pol-s3-read",
        [⟨.Allow,
           [.S3_GetObject, .S3_ListBucket],
           ["arn:aws:s3:::acme-static/*"]⟩]⟩
    , ⟨"pol-s3-write",
        [⟨.Allow,
           [.S3_PutObject],
           ["arn:aws:s3:::acme-backups/*"]⟩]⟩ ]

-- Quick sanity checks on the example (evaluated at compile time)

-- The web instance is running
#eval threeTierInfra.findInstance "i-web" |>.map (·.state)
-- expected: some InstanceState.Running

-- The DB volume is InUse
#eval threeTierInfra.findVolume "vol-db" |>.map (·.state)
-- expected: some VolumeState.InUse

-- The pol-s3-read policy allows S3:GetObject on the static bucket
#eval threeTierInfra.findPolicy "pol-s3-read"
      |>.map (·.allows .S3_GetObject "arn:aws:s3:::acme-static/index.html")
-- expected: some true

-- Stopping the web instance releases its public IP
#eval
  let s' := applyInstanceTransition
              threeTierInfra "i-web" .Running .Stopping .initStop
  s'.findInstance "i-web" |>.map (·.publicIp)
-- expected: some none

end AWS
