use vstd::prelude::*;
use vstd::multiset::Multiset;

fn main() {}

verus!{

pub type InstalledTypes = Map<StringView, InstalledType>;

pub type PodStatusView = EmptyStatusView;

pub type StoredState = Map<ObjectRef, DynamicObjectView>;

pub type ActionPred<T> = spec_fn(T, T) -> bool;

pub type StatePred<T> = spec_fn(T) -> bool;

pub type UnmarshalError = ();

pub type ExternalResponse = Value;

pub type ExternalRequest = Value;

pub type ExternalLocalState = Value;

pub type VReplicaSetStatusView = EmptyStatusView;

pub type RPCId = nat;

pub type Uid = int;

pub type Value = StringView;

pub type StringView = Seq<char>;

pub type ResourceVersion = int;

pub type ReconcileLocalState = Value;

pub type ReconcileId = nat;

pub type EmptyStatusView = ();



// File: kubernetes_api_objects/spec/resource.rs
pub trait ResourceView: Sized {

    spec fn metadata(self) -> ObjectMetaView;

    spec fn kind() -> Kind;

    spec fn object_ref(self) -> ObjectRef;

}


macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {

            open spec fn metadata(self) -> ObjectMetaView {
                self.metadata
            }

            open spec fn kind() -> Kind {
                $kind
            }

            open spec fn object_ref(self) -> ObjectRef {
                ObjectRef {
                    kind: Self::kind(),
                    name: self.metadata().name->0,
                    namespace: self.metadata().namespace->0,
                }
            }

}}}}




// File: kubernetes_cluster/spec/api_server/types.rs
pub struct APIServerState {
    pub resources: StoredState,
    pub uid_counter: Uid,
    pub resource_version_counter: ResourceVersion,
}

pub struct InstalledType {
    pub unmarshallable_spec: spec_fn(Value) -> bool,
    pub unmarshallable_status: spec_fn(Value) -> bool,
    pub valid_object: spec_fn(DynamicObjectView) -> bool,
    pub valid_transition: spec_fn(DynamicObjectView, DynamicObjectView) -> bool,
    pub marshalled_default_status: spec_fn() -> Value,
}


// File: kubernetes_cluster/spec/controller/types.rs
pub struct ControllerState {
    pub ongoing_reconciles: Map<ObjectRef, OngoingReconcile>,
    pub scheduled_reconciles: Map<ObjectRef, DynamicObjectView>,
    pub reconcile_id_allocator: ReconcileIdAllocator,
}

pub enum RequestContent {
    KubernetesRequest(APIRequest),
    ExternalRequest(ExternalRequest),
}

pub enum ResponseContent {
    KubernetesResponse(APIResponse),
    ExternalResponse(ExternalResponse),
}

pub struct ReconcileIdAllocator {
    pub reconcile_id_counter: ReconcileId,
}

pub struct ReconcileModel {
    pub kind: Kind,
    pub init: spec_fn() -> ReconcileLocalState,
    pub transition: spec_fn(DynamicObjectView, Option<ResponseContent>, ReconcileLocalState) -> (ReconcileLocalState, Option<RequestContent>),
    pub done: spec_fn(ReconcileLocalState) -> bool,
    pub error: spec_fn(ReconcileLocalState) -> bool,
}

pub struct OngoingReconcile {
    pub triggering_cr: DynamicObjectView,
    pub pending_req_msg: Option<Message>,
    pub local_state: ReconcileLocalState,
    pub reconcile_id: ReconcileId,
}


// File: kubernetes_cluster/spec/external/types.rs
pub struct ExternalState {
    pub state: ExternalLocalState,
}

pub struct ExternalModel {
    pub init: spec_fn() -> ExternalLocalState,
    pub transition: spec_fn(ExternalRequest, ExternalLocalState, StoredState) -> (ExternalLocalState, ExternalResponse),
}


// File: kubernetes_cluster/spec/network/types.rs
pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}


// File: kubernetes_api_objects/spec/affinity.rs
pub struct AffinityView {}


// File: kubernetes_api_objects/spec/api_method.rs
#[is_variant]
pub enum APIRequest {
    GetRequest(GetRequest),
    ListRequest(ListRequest),
    CreateRequest(CreateRequest),
    DeleteRequest(DeleteRequest),
    UpdateRequest(UpdateRequest),
    UpdateStatusRequest(UpdateStatusRequest),
    GetThenDeleteRequest(GetThenDeleteRequest),
    GetThenUpdateRequest(GetThenUpdateRequest),
}

pub struct GetRequest {
    pub key: ObjectRef,
}

pub struct ListRequest {
    pub kind: Kind,
    pub namespace: StringView,
}

pub struct CreateRequest {
    pub namespace: StringView,
    pub obj: DynamicObjectView,
}

impl CreateRequest {

    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            name: self.obj.metadata.name->0,
            namespace: self.namespace,
            kind: self.obj.kind,
        }
    }

}


pub struct DeleteRequest {
    pub key: ObjectRef,
    pub preconditions: Option<PreconditionsView>,
}

pub struct UpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

impl UpdateRequest {

    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }

}


pub struct UpdateStatusRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

impl UpdateStatusRequest {

    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }

}


pub struct GetThenDeleteRequest {
    pub key: ObjectRef,
    pub owner_ref: OwnerReferenceView,
}

pub struct GetThenUpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub owner_ref: OwnerReferenceView,
    pub obj: DynamicObjectView,
}

impl GetThenUpdateRequest {

    pub open spec fn key(self) -> ObjectRef {
        ObjectRef {
            kind: self.obj.kind,
            namespace: self.namespace,
            name: self.name,
        }
    }

}


#[is_variant]
pub enum APIResponse {
    GetResponse(GetResponse),
    ListResponse(ListResponse),
    CreateResponse(CreateResponse),
    DeleteResponse(DeleteResponse),
    UpdateResponse(UpdateResponse),
    UpdateStatusResponse(UpdateStatusResponse),
    GetThenDeleteResponse(GetThenDeleteResponse),
    GetThenUpdateResponse(GetThenUpdateResponse),
}

pub struct GetResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct ListResponse {
    pub res: Result<Seq<DynamicObjectView>, APIError>,
}

pub struct CreateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct DeleteResponse {
    pub res: Result<(), APIError>,
}

pub struct UpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct UpdateStatusResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct GetThenUpdateResponse {
    pub res: Result<DynamicObjectView, APIError>,
}

pub struct GetThenDeleteResponse {
    pub res: Result<(), APIError>,
}


// File: kubernetes_api_objects/spec/common.rs
#[is_variant]
pub enum Kind {
    ConfigMapKind,
    CustomResourceKind(StringView),
    DaemonSetKind,
    PersistentVolumeClaimKind,
    PodKind,
    RoleKind,
    RoleBindingKind,
    StatefulSetKind,
    ServiceKind,
    ServiceAccountKind,
    SecretKind,
}

pub struct ObjectRef {
    pub kind: Kind,
    pub name: StringView,
    pub namespace: StringView,
}


// File: kubernetes_api_objects/spec/container.rs
pub struct ContainerView {
    pub env: Option<Seq<EnvVarView>>,
    pub image: Option<StringView>,
    pub name: StringView,
    pub ports: Option<Seq<ContainerPortView>>,
    pub volume_mounts: Option<Seq<VolumeMountView>>,
    pub lifecycle: Option<LifecycleView>,
    pub resources: Option<ResourceRequirementsView>,
    pub readiness_probe: Option<ProbeView>,
    pub liveness_probe: Option<ProbeView>,
    pub command: Option<Seq<StringView>>,
    pub image_pull_policy: Option<StringView>,
    pub args: Option<Seq<StringView>>,
    pub security_context: Option<SecurityContextView>,
}

pub struct LifecycleView {
    pub pre_stop: Option<LifecycleHandlerView>,
}

pub struct LifecycleHandlerView {
    pub exec_: Option<ExecActionView>,
}

pub struct ContainerPortView {
    pub container_port: int,
    pub name: Option<StringView>,
    pub protocol: Option<StringView>,
}

pub struct VolumeMountView {
    pub mount_path: StringView,
    pub name: StringView,
    pub read_only: Option<bool>,
    pub sub_path: Option<StringView>,
    pub mount_propagation: Option<StringView>,
}

pub struct ProbeView {
    pub exec_: Option<ExecActionView>,
    pub failure_threshold: Option<int>,
    pub initial_delay_seconds: Option<int>,
    pub period_seconds: Option<int>,
    pub success_threshold: Option<int>,
    pub tcp_socket: Option<TCPSocketActionView>,
    pub timeout_seconds: Option<int>,
}

pub struct ExecActionView {
    pub command: Option<Seq<StringView>>,
}

pub struct TCPSocketActionView {
    pub host: Option<StringView>,
    pub port: int,
}

pub struct EnvVarView {
    pub name: StringView,
    pub value: Option<StringView>,
    pub value_from: Option<EnvVarSourceView>,
}

pub struct EnvVarSourceView {
    pub field_ref: Option<ObjectFieldSelectorView>,
}

pub struct SecurityContextView {}


// File: kubernetes_api_objects/spec/dynamic.rs
pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}


// File: kubernetes_api_objects/spec/label_selector.rs
pub struct LabelSelectorView {
    pub match_labels: Option<Map<StringView, StringView>>,
}


// File: kubernetes_api_objects/spec/object_meta.rs
pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub generate_name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub resource_version: Option<ResourceVersion>,
    pub uid: Option<Uid>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub deletion_timestamp: Option<StringView>,
}

impl ObjectMetaView {

    pub open spec fn owner_references_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs.contains(owner_ref),
            None => false,
        }
    }

}



// File: kubernetes_api_objects/spec/owner_reference.rs
pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}


// File: kubernetes_api_objects/spec/pod.rs
pub struct PodSpecView {
    pub affinity: Option<AffinityView>,
    pub containers: Seq<ContainerView>,
    pub volumes: Option<Seq<VolumeView>>,
    pub init_containers: Option<Seq<ContainerView>>,
    pub service_account_name: Option<StringView>,
    pub tolerations: Option<Seq<TolerationView>>,
    pub node_selector: Option<Map<StringView, StringView>>,
    pub runtime_class_name: Option<StringView>,
    pub dns_policy: Option<StringView>,
    pub priority_class_name: Option<StringView>,
    pub scheduler_name: Option<StringView>,
    pub security_context: Option<PodSecurityContextView>,
    pub host_network: Option<bool>,
    pub termination_grace_period_seconds: Option<int>,
    pub image_pull_secrets: Option<Seq<LocalObjectReferenceView>>,
    pub hostname: Option<StringView>,
    pub subdomain: Option<StringView>,
}

pub struct PodSecurityContextView {}

pub struct LocalObjectReferenceView {}


// File: kubernetes_api_objects/spec/pod_template_spec.rs
pub struct PodTemplateSpecView {
    pub metadata: Option<ObjectMetaView>,
    pub spec: Option<PodSpecView>,
}


// File: kubernetes_api_objects/spec/preconditions.rs
pub struct PreconditionsView {
    pub uid: Option<Uid>,
    pub resource_version: Option<ResourceVersion>,
}


// File: kubernetes_api_objects/spec/resource_requirements.rs
pub struct ResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
}


// File: kubernetes_api_objects/spec/toleration.rs
pub struct TolerationView {}


// File: kubernetes_api_objects/spec/volume.rs
pub struct VolumeView {
    pub host_path: Option<HostPathVolumeSourceView>,
    pub config_map: Option<ConfigMapVolumeSourceView>,
    pub name: StringView,
    pub projected: Option<ProjectedVolumeSourceView>,
    pub secret: Option<SecretVolumeSourceView>,
    pub downward_api: Option<DownwardAPIVolumeSourceView>,
    pub empty_dir: Option<EmptyDirVolumeSourceView>,
    pub persistent_volume_claim: Option<PersistentVolumeClaimVolumeSourceView>,
}

pub struct EmptyDirVolumeSourceView {
    pub medium: Option<StringView>,
    pub size_limit: Option<StringView>,
}

pub struct HostPathVolumeSourceView {
    pub path: StringView,
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

pub struct SecretVolumeSourceView {
    pub secret_name: Option<StringView>,
}

pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

pub struct KeyToPathView {
    pub key: StringView,
    pub path: StringView,
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}

pub struct ObjectFieldSelectorView {
    pub field_path: StringView,
    pub api_version: Option<StringView>,
}

pub struct PersistentVolumeClaimVolumeSourceView {
    pub claim_name: StringView,
    pub read_only: Option<bool>,
}


// File: kubernetes_cluster/spec/cluster.rs
pub struct ClusterState {
    pub api_server: APIServerState,
    pub controller_and_externals: Map<int, ControllerAndExternalState>,
    pub network: NetworkState,
    pub rpc_id_allocator: RPCIdAllocator,
    pub req_drop_enabled: bool,
    pub pod_monkey_enabled: bool,
}

pub struct ControllerAndExternalState {
    pub controller: ControllerState,
    pub external: Option<ExternalState>,
    pub crash_enabled: bool,
}

impl ClusterState {

    #[verifier(inline)]
    pub open spec fn in_flight(self) -> Multiset<Message> {
        self.network.in_flight
    }

    #[verifier(inline)]
    pub open spec fn resources(self) -> StoredState {
        self.api_server.resources
    }

}


pub struct Cluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

pub struct ControllerModel {
    pub reconcile_model: ReconcileModel,
    pub external_model: Option<ExternalModel>,
}


// File: kubernetes_cluster/spec/message.rs
pub struct Message {
    pub src: HostId,
    pub dst: HostId,
    pub rpc_id: RPCId,
    pub content: MessageContent,
}

#[is_variant]
pub enum HostId {
    APIServer,
    BuiltinController,
    Controller(int, ObjectRef),
    External(int),
    PodMonkey,
}

pub struct RPCIdAllocator {
    pub rpc_id_counter: RPCId,
}

#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalRequest),
    ExternalResponse(ExternalResponse),
}


// File: controllers/vreplicaset_controller/trusted/spec_types.rs
pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

implement_resource_view_trait!(VReplicaSetView, VReplicaSetSpecView, VReplicaSetSpecView::default(),
    Option<VReplicaSetStatusView>, None, VReplicaSetView::_kind(), _state_validation, _transition_validation);


impl VReplicaSetView {

    pub open spec fn controller_owner_ref(self) -> OwnerReferenceView {
        OwnerReferenceView {
            block_owner_deletion: Some(true),
            controller: Some(true),
            kind: Self::kind(),
            name: self.metadata.name->0,
            uid: self.metadata.uid->0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

}


pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}


// File: kubernetes_api_objects/error.rs
#[is_variant]
pub enum APIError {
    BadRequest,
    Conflict,
    Forbidden,
    Invalid,
    ObjectNotFound,
    ObjectAlreadyExists,
    NotSupported,
    InternalError,
    Timeout,
    ServerTimeout,
    TransactionAbort,
    Other
}


// File: temporal_logic/defs.rs
pub struct Execution<T> {
    pub nat_to_state: spec_fn(nat) -> T,
}

impl<T> Execution<T> {

    pub open spec fn head(self) -> T {
        (self.nat_to_state)(0)
    }

    pub open spec fn suffix(self, pos: nat) -> Self {
        Execution {
            nat_to_state: |i: nat| (self.nat_to_state)(i + pos),
        }
    }

}


#[verifier(reject_recursive_types(T))]
pub struct TempPred<T> {
    pub pred: spec_fn(Execution<T>) -> bool,
}

impl<T> TempPred<T> {

    pub open spec fn new(pred: spec_fn(Execution<T>) -> bool) -> Self {
        TempPred {
            pred: pred,
        }
    }

    pub open spec fn satisfied_by(self, execution: Execution<T>) -> bool {
        (self.pred)(execution)
    }

    pub open spec fn implies(self, other: Self) -> Self {
        TempPred::new(|ex: Execution<T>| self.satisfied_by(ex) ==> other.satisfied_by(ex))
    }

}


pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn stable<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| temp_pred.implies(always(temp_pred)).satisfied_by(ex))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: controllers/vreplicaset_controller/proof/helper_invariants/predicate.rs
pub open spec fn no_other_pending_create_request_interferes_with_vrs_reconcile(
    req: CreateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == Kind::PodKind
            && req.key().namespace == vrs.metadata.namespace.unwrap()) ==> !{
            let owner_references = req.obj.metadata.owner_references->0;
            &&& req.obj.metadata.owner_references is Some
            &&& owner_references.contains(vrs.controller_owner_ref())
        }
    }
}

pub open spec fn no_other_pending_update_request_interferes_with_vrs_reconcile(
    req: UpdateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == Kind::PodKind
            && req.key().namespace == vrs.metadata.namespace.unwrap()) ==>
            req.obj.metadata.resource_version is Some
            // Prevents 1): where a message not from our specific vrs updates
            // a vrs-owned pod.
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.namespace == vrs.metadata.namespace
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& owner_references.contains(vrs.controller_owner_ref())
            }
            // Prevents 2): where any message not from our specific vrs updates 
            // pods so they become owned by another VReplicaSet.
            && (req.obj.metadata.owner_references is Some ==>
                        ! req.obj.metadata.owner_references->0.contains(vrs.controller_owner_ref()))
    }
}

pub open spec fn no_other_pending_update_status_request_interferes_with_vrs_reconcile(
    req: UpdateStatusRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == Kind::PodKind
            && req.key().namespace == vrs.metadata.namespace.unwrap()) ==> 
            req.obj.metadata.resource_version is Some
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.namespace == vrs.metadata.namespace
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& owner_references.contains(vrs.controller_owner_ref())
            }
    }
}

pub open spec fn no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(
    req: GetThenUpdateRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == Kind::PodKind ==> {
            // Prevents 1): where a message not from our specific vrs updates
            // a vrs-owned pod.
            &&& (req.key().namespace == vrs.metadata.namespace.unwrap() ==> {
                &&& req.owner_ref.controller is Some
                &&& req.owner_ref.controller->0
                &&& req.owner_ref != vrs.controller_owner_ref()
            })
            // Prevents 2): where any message not from our specific vrs updates 
            // pods so they become owned by another VReplicaSet.
            &&& (req.obj.metadata.owner_references is Some ==>
                    ! req.obj.metadata.owner_references->0.contains(vrs.controller_owner_ref()))
        }
    }
}

pub open spec fn no_other_pending_delete_request_interferes_with_vrs_reconcile(
    req: DeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.key.kind == Kind::PodKind
            && req.key.namespace == vrs.metadata.namespace.unwrap()) ==>
            req.preconditions is Some
            && {
                ||| {
                    req.preconditions->0.resource_version is Some
                    && !{
                        let etcd_obj = s.resources()[req.key];
                        let owner_references = etcd_obj.metadata.owner_references->0;
                        &&& s.resources().contains_key(req.key)
                        &&& etcd_obj.metadata.namespace == vrs.metadata.namespace
                        &&& etcd_obj.metadata.resource_version is Some
                        &&& etcd_obj.metadata.resource_version
                            == req.preconditions->0.resource_version
                        &&& etcd_obj.metadata.owner_references is Some
                        &&& owner_references.contains(vrs.controller_owner_ref())
                    }
                }
                ||| { // required to handle garbage collector's messages.
                    &&& req.preconditions.unwrap().uid is Some
                    &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
                    &&& s.resources().contains_key(req.key) ==> {
                        let obj = s.resources()[req.key];
                        ||| !(obj.metadata.owner_references_contains(vrs.controller_owner_ref())
                                && obj.kind == Kind::PodKind 
                                && obj.metadata.namespace == vrs.metadata.namespace)
                        ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
                    }
                }
            }
    }
}

pub open spec fn no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(
    req: GetThenDeleteRequest,
    vrs: VReplicaSetView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.key.kind == Kind::PodKind
            && req.key.namespace == vrs.metadata.namespace.unwrap()) ==> {
            &&& req.owner_ref.controller is Some
            &&& req.owner_ref.controller->0
            &&& req.owner_ref != vrs.controller_owner_ref()
        }
    }
}

pub open spec fn no_other_pending_request_interferes_with_vrs_reconcile(
    vrs: VReplicaSetView,
    controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src != HostId::Controller(controller_id, vrs.object_ref())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let content = msg.content;
            match content.get_APIRequest_0() {
                APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
                APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vrs_reconcile(req, vrs)(s),
                _ => true,
            }
        }
    }
}


// File: temporal_logic/rules.rs
	#[verifier::external_body]
pub proof fn always_p_is_stable<T>(p: TempPred<T>)
    ensures valid(stable(always(p))),
	{
		unimplemented!()
	}


// File: controllers/vreplicaset_controller/proof/liveness/spec.rs
pub open spec fn invariants_since_phase_v(vrs: VReplicaSetView, cluster: Cluster, controller_id: int) -> TempPred<ClusterState>
{
    always(lift_state(no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)))
}

pub proof fn invariants_since_phase_v_is_stable(vrs: VReplicaSetView, cluster: Cluster, controller_id: int)
    ensures valid(stable(invariants_since_phase_v(vrs, cluster, controller_id))),
{
}


}
