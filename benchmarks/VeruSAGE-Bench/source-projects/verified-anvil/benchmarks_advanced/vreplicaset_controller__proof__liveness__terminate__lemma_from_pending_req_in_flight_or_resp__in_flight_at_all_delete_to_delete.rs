use vstd::prelude::*;
use vstd::multiset::Multiset;

fn main() {}

verus!{

pub trait CustomResourceView : ResourceView {}

pub type ServiceStatusView = EmptyStatusView;

type ServiceAccountSpecView = Option<bool>;

pub type PodStatusView = EmptyStatusView;

type ConfigMapSpecView = Option<Map<StringView, StringView>>;

type SecretSpecView = Option<Map<StringView, StringView>>;

pub type PersistentVolumeClaimStatusView = EmptyStatusView;

pub type UnmarshalError = ();

pub type ActionPred<T> = spec_fn(T, T) -> bool;

pub type StatePred<T> = spec_fn(T) -> bool;
pub type VReplicaSetStatusView = EmptyStatusView;

pub type RPCId = nat;
pub type ExternalResponse = Value;

pub type ExternalRequest = Value;

pub type InstalledTypes = Map<StringView, InstalledType>;

pub type StringView = Seq<char>;

pub type ResourceVersion = int;

pub type Uid = int;

pub type Value = StringView;

pub type ExternalLocalState = Value;

pub type StoredState = Map<ObjectRef, DynamicObjectView>;

pub type EmptyStatusView = ();

pub type ReconcileLocalState = Value;

pub type ReconcileId = nat;


// File: kubernetes_api_objects/spec/resource.rs
pub trait Marshallable: Sized {

    spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}

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

pub struct DeleteRequest {
    pub key: ObjectRef,
    pub preconditions: Option<PreconditionsView>,
}

pub struct UpdateRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
}

pub struct UpdateStatusRequest {
    pub namespace: StringView,
    pub name: StringView,
    pub obj: DynamicObjectView,
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


// File: kubernetes_api_objects/spec/owner_reference.rs
pub struct OwnerReferenceView {
    pub block_owner_deletion: Option<bool>,
    pub controller: Option<bool>,
    pub kind: Kind,
    pub name: StringView,
    pub uid: Uid,
}


// File: kubernetes_api_objects/spec/pod.rs
pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

implement_resource_view_trait!(PodView, Option<PodSpecView>, None, Option<PodStatusView>, None,
    Kind::PodKind, _state_validation, _transition_validation);

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
    pub open spec fn ongoing_reconciles(self, controller_id: int) -> Map<ObjectRef, OngoingReconcile> {
        self.controller_and_externals[controller_id].controller.ongoing_reconciles
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

pub open spec fn resp_msg_matches_req_msg(resp_msg: Message, req_msg: Message) -> bool {
    ||| {
        &&& resp_msg.content.is_APIResponse()
        &&& req_msg.content.is_APIRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
        &&& match resp_msg.content.get_APIResponse_0() {
            APIResponse::GetResponse(_) => req_msg.content.get_APIRequest_0().is_GetRequest(),
            APIResponse::ListResponse(_) => req_msg.content.get_APIRequest_0().is_ListRequest(),
            APIResponse::CreateResponse(_) => req_msg.content.get_APIRequest_0().is_CreateRequest(),
            APIResponse::DeleteResponse(_) => req_msg.content.get_APIRequest_0().is_DeleteRequest(),
            APIResponse::UpdateResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateRequest(),
            APIResponse::UpdateStatusResponse(_) => req_msg.content.get_APIRequest_0().is_UpdateStatusRequest(),
            APIResponse::GetThenDeleteResponse(_) => req_msg.content.get_APIRequest_0().is_GetThenDeleteRequest(),
            APIResponse::GetThenUpdateResponse(_) => req_msg.content.get_APIRequest_0().is_GetThenUpdateRequest(),
        }
    }
    ||| {
        &&& resp_msg.content.is_ExternalResponse()
        &&& req_msg.content.is_ExternalRequest()
        &&& resp_msg.dst == req_msg.src
        &&& resp_msg.src == req_msg.dst
        &&& resp_msg.rpc_id == req_msg.rpc_id
    }
}


// File: controllers/vreplicaset_controller/model/reconciler.rs
pub struct VReplicaSetReconcileState {
    pub reconcile_step: VReplicaSetRecStepView,
    pub filtered_pods: Option<Seq<PodView>>,
}


// File: controllers/vreplicaset_controller/trusted/spec_types.rs
pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

impl CustomResourceView for VReplicaSetView {}

implement_resource_view_trait!(VReplicaSetView, VReplicaSetSpecView, VReplicaSetSpecView::default(),
    Option<VReplicaSetStatusView>, None, VReplicaSetView::_kind(), _state_validation, _transition_validation);


impl VReplicaSetView {

    #[verifier(inline)]
    pub open spec fn _kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

}


pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}


// File: controllers/vreplicaset_controller/trusted/step.rs
#[is_variant]
pub enum VReplicaSetRecStepView {
    Init,
    AfterListPods,
    AfterCreatePod(nat),
    AfterDeletePod(nat),
    Done,
    Error,
}


// File: kubernetes_api_objects/error.rs
#[is_variant]
#[derive(Debug)]
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

    pub open spec fn entails(self, other: Self) -> bool {
        valid(self.implies(other))
    }

}


pub open spec fn lift_state<T>(state_pred: StatePred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| state_pred(ex.head()))
}

pub open spec fn always<T>(temp_pred: TempPred<T>) -> TempPred<T> {
    TempPred::new(|ex: Execution<T>| forall |i: nat| #[trigger] temp_pred.satisfied_by(ex.suffix(i)))
}

pub open spec fn valid<T>(temp_pred: TempPred<T>) -> bool {
    forall |ex: Execution<T>| temp_pred.satisfied_by(ex)
}


// File: controllers/vreplicaset_controller/model/install.rs
impl Marshallable for VReplicaSetReconcileState {

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}


// File: controllers/vreplicaset_controller/proof/predicate.rs
pub open spec fn at_step_closure(step: VReplicaSetRecStepView) -> spec_fn(ReconcileLocalState) -> bool {
    |s: ReconcileLocalState| VReplicaSetReconcileState::unmarshal(s).unwrap().reconcile_step == step
}

pub open spec fn unwrap_local_state_closure<T>(
    closure: spec_fn(VReplicaSetReconcileState) -> T
) -> spec_fn(ReconcileLocalState) -> T {
    |s: ReconcileLocalState| closure(VReplicaSetReconcileState::unmarshal(s).unwrap())
}


// File: kubernetes_cluster/proof/controller_runtime_liveness.rs
impl Cluster {

pub open spec fn has_pending_req_msg(controller_id: int, s: ClusterState, key: ObjectRef) -> bool {
    &&& s.ongoing_reconciles(controller_id)[key].pending_req_msg is Some
    &&& (s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content.is_APIRequest()
        || s.ongoing_reconciles(controller_id)[key].pending_req_msg->0.content.is_ExternalRequest())
}

pub open spec fn request_sent_by_controller_with_key(controller_id: int, key: ObjectRef, msg: Message) -> bool {
    &&& msg.src == HostId::Controller(controller_id, key)
    &&& {
        ||| {
            &&& msg.dst == HostId::APIServer
            &&& msg.content.is_APIRequest()
        }
        ||| {
            &&& msg.dst == HostId::External(controller_id)
            &&& msg.content.is_ExternalRequest()
        }
    }
}

pub open spec fn at_expected_reconcile_states(controller_id: int, key: ObjectRef, expected_states: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& s.ongoing_reconciles(controller_id).contains_key(key)
        &&& expected_states(s.ongoing_reconciles(controller_id)[key].local_state)
    }
}

pub open spec fn pending_req_in_flight_or_resp_in_flight_at_reconcile_state(controller_id: int, key: ObjectRef, current_state: spec_fn(ReconcileLocalState) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        Self::at_expected_reconcile_states(controller_id, key, current_state)(s)
        ==> {
            let msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
            &&& Self::has_pending_req_msg(controller_id, s, key)
            &&& Self::request_sent_by_controller_with_key(controller_id, key, msg)
            &&& (s.in_flight().contains(msg)
                || exists |resp_msg: Message| {
                    &&& #[trigger] s.in_flight().contains(resp_msg)
                    &&& resp_msg_matches_req_msg(resp_msg, msg)
                })
        }
    }
}

}

// File: controllers/vreplicaset_controller/proof/liveness/terminate.rs
pub proof fn lemma_from_pending_req_in_flight_or_resp_in_flight_at_all_delete_to_delete_n(
    spec: TempPred<ClusterState>, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, n: nat
)
    requires
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                unwrap_local_state_closure(
                    |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
                )
            )))),
    ensures
        spec.entails(always(
            lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
                controller_id,
                vrs.object_ref(),
                at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n))
            )))),
{
    let pre = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        unwrap_local_state_closure(
            |s: VReplicaSetReconcileState| s.reconcile_step.is_AfterDeletePod()
        )
    ));
    let post = lift_state(Cluster::pending_req_in_flight_or_resp_in_flight_at_reconcile_state(
        controller_id,
        vrs.object_ref(),
        at_step_closure(VReplicaSetRecStepView::AfterDeletePod(n))
    ));

    assert forall |ex| #![auto] spec.satisfied_by(ex) && spec.entails(always(pre)) implies always(post).satisfied_by(ex) by {
        assert(forall |ex| #[trigger] spec.implies(always(pre)).satisfied_by(ex));
        assert(forall |ex| spec.implies(always(pre)).satisfied_by(ex) <==> (spec.satisfied_by(ex) ==> #[trigger] always(pre).satisfied_by(ex)));
        assert(always(pre).satisfied_by(ex));

        assert forall |i: nat| #![auto] pre.satisfied_by(ex.suffix(i)) implies post.satisfied_by(ex.suffix(i)) by {
        }
    }
}


}
