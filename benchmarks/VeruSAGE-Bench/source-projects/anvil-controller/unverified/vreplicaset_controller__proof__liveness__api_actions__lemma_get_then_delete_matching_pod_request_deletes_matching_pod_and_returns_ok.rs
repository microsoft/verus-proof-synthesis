use vstd::prelude::*;
use vstd::multiset::Multiset;
use vstd::map_lib::lemma_values_finite;


fn main() {}

verus!{

type RoleSpecView = Option<Seq<PolicyRuleView>>;

type RoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

pub type ServiceStatusView = EmptyStatusView;

type ServiceAccountSpecView = Option<bool>;

pub type ControllerStateMachine = StateMachine<ControllerState, ControllerActionInput, ControllerActionInput, ControllerActionOutput, ControllerStep>;

pub type ControllerAction = Action<ControllerState, ControllerActionInput, ControllerActionOutput>;


pub type ExternalStateMachine = StateMachine<ExternalState, ExternalActionInput, ExternalActionInput, ExternalActionOutput, ExternalStep>;

pub type ExternalAction = Action<ExternalState, ExternalActionInput, ExternalActionOutput>;


pub type APIServerStateMachine = StateMachine<APIServerState, APIServerActionInput, APIServerActionInput, APIServerActionOutput, APIServerStep>;

pub type APIServerAction = Action<APIServerState, APIServerActionInput, APIServerActionOutput>;

pub type BuiltinControllersStateMachine = StateMachine<(),
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionInput,
                                            BuiltinControllersActionOutput,
                                            BuiltinControllersStep>;

pub type BuiltinControllersAction = Action<(),
                                        BuiltinControllersActionInput,
                                        BuiltinControllersActionOutput>;


pub type PodStatusView = EmptyStatusView;

pub type PodMonkeyState = ();

type ConfigMapSpecView = Option<Map<StringView, StringView>>;

type SecretSpecView = Option<Map<StringView, StringView>>;

pub type PersistentVolumeClaimStatusView = EmptyStatusView;

pub type UnmarshalError = ();

pub type PodMonkeyAction = Action<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionOutput>;
pub type PodMonkeyStateMachine = StateMachine<PodMonkeyState, PodMonkeyActionInput, PodMonkeyActionInput, PodMonkeyActionOutput, PodMonkeyStep>;


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


// File:: vstd_ext/map_lib.rs
#[verifier::external_body]
pub proof fn a_submap_of_a_finite_map_is_finite<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        m1.submap_of(m2),
        m2.dom().finite(),
    ensures
        m1.dom().finite(),
{ unimplemented!()}


// File: kubernetes_api_objects/spec/resource.rs
pub trait Marshallable: Sized {

    spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}


pub trait ResourceView: Sized {

    type Spec;

    type Status;

    spec fn default() -> Self;

    spec fn metadata(self) -> ObjectMetaView;

    spec fn kind() -> Kind;

    spec fn object_ref(self) -> ObjectRef;

    spec fn spec(self) -> Self::Spec;

    spec fn status(self) -> Self::Status;

    spec fn marshal(self) -> DynamicObjectView;

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    spec fn marshal_spec(s: Self::Spec) -> Value;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn marshal_status(s: Self::Status) -> Value;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

    spec fn state_validation(self) -> bool;

    spec fn transition_validation(self, old_obj: Self) -> bool;

}


pub open spec fn empty_status() -> EmptyStatusView {
    ()
}

macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;

            open spec fn default() -> Self {
                Self {
                    metadata: ObjectMetaView::default(),
                    spec: $spec_default,
                    status: $status_default,
                }
            }

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

            open spec fn spec(self) -> Self::Spec {
                self.spec
            }

            open spec fn status(self) -> Self::Status {
                self.status
            }

            open spec fn marshal(self) -> DynamicObjectView {
                DynamicObjectView {
                    kind: Self::kind(),
                    metadata: self.metadata(),
                    spec: Self::marshal_spec(self.spec()),
                    status: Self::marshal_status(self.status()),
                }
            }

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self {
                        metadata: obj.metadata,
                        spec: Self::unmarshal_spec(obj.spec)->Ok_0,
                        status: Self::unmarshal_status(obj.status)->Ok_0,
                    })
                }
            }

            uninterp spec fn marshal_spec(s: Self::Spec) -> Value;

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn marshal_status(s: Self::Status) -> Value;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

            open spec fn transition_validation(self, old_obj: Self) -> bool {
                self.$transition_validation(old_obj)
            }
        }

        }
    };
    ($t:ty, $spec_t:ty, $status_t:ty, $default:ident, $kind:expr, $spec:ident, $status:ident, $unmarshal:ident, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;

            open spec fn default() -> Self {
                Self::$default()
            }

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

            open spec fn spec(self) -> Self::Spec {
                self.$spec()
            }

            open spec fn status(self) -> Self::Status {
                self.$status()
            }

            open spec fn marshal(self) -> DynamicObjectView {
                DynamicObjectView {
                    kind: Self::kind(),
                    metadata: self.metadata(),
                    spec: Self::marshal_spec(self.spec()),
                    status: Self::marshal_status(self.status()),
                }
            }

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self::$unmarshal(obj))
                }
            }

            uninterp spec fn marshal_spec(s: Self::Spec) -> Value;

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn marshal_status(s: Self::Status) -> Value;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

            open spec fn transition_validation(self, old_obj: Self) -> bool {
                self.$transition_validation(old_obj)
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

pub enum APIServerStep {
    HandleRequest,
}

pub struct APIServerActionInput {
    pub recv: Option<Message>,
}

pub struct APIServerActionOutput {
    pub send: Multiset<Message>
}


// File: kubernetes_cluster/spec/builtin_controllers/types.rs
#[is_variant]
pub enum BuiltinControllersStep {
    RunGarbageCollector,
}

#[is_variant]
pub enum BuiltinControllerChoice {
    GarbageCollector,
}

pub struct BuiltinControllersActionInput {
    pub choice: BuiltinControllerChoice,
    pub key: ObjectRef,
    pub rpc_id_allocator: RPCIdAllocator,
    pub resources: StoredState,
}

pub struct BuiltinControllersActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
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

impl ReconcileIdAllocator {

    pub open spec fn allocate(self) -> (Self, ReconcileId) {
        (ReconcileIdAllocator {
            reconcile_id_counter: self.reconcile_id_counter + 1,
        }, self.reconcile_id_counter)
    }

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

#[is_variant]
pub enum ControllerStep {
    RunScheduledReconcile,
    ContinueReconcile,
    EndReconcile,
}

pub struct ControllerActionInput {
    pub recv: Option<Message>,
    pub scheduled_cr_key: Option<ObjectRef>,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub struct ControllerActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
}


// File: kubernetes_cluster/spec/external/types.rs
pub struct ExternalState {
    pub state: ExternalLocalState,
}

pub struct ExternalModel {
    pub init: spec_fn() -> ExternalLocalState,
    pub transition: spec_fn(ExternalRequest, ExternalLocalState, StoredState) -> (ExternalLocalState, ExternalResponse),
}

pub enum ExternalStep {
    HandleExternalRequest,
}

pub struct ExternalActionInput {
    pub recv: Option<Message>,
    pub resources: StoredState,
}

pub struct ExternalActionOutput {
    pub send: Multiset<Message>,
}


// File: kubernetes_cluster/spec/network/types.rs
pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}


// File: kubernetes_cluster/spec/pod_monkey/types.rs
pub enum PodMonkeyStep {
    CreatePod,
    UpdatePod,
    UpdatePodStatus,
    DeletePod,
}

pub struct PodMonkeyActionInput {
    pub pod: PodView,
    pub rpc_id_allocator: RPCIdAllocator,
}

pub struct PodMonkeyActionOutput {
    pub send: Multiset<Message>,
    pub rpc_id_allocator: RPCIdAllocator,
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

impl GetThenDeleteRequest {

    pub open spec fn key(self) -> ObjectRef {
        self.key
    }

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


// File: kubernetes_api_objects/spec/config_map.rs
pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

implement_resource_view_trait!(ConfigMapView, ConfigMapSpecView, EmptyStatusView, _default, Kind::ConfigMapKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);


impl ConfigMapView {

    #[verifier(inline)]
    pub open spec fn _default() -> ConfigMapView {
        ConfigMapView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> ConfigMapSpecView {
        self.data
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ConfigMapView {
        ConfigMapView {
            metadata: obj.metadata,
            data: ConfigMapView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ConfigMapView) -> bool { true }

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


// File: kubernetes_api_objects/spec/daemon_set.rs
pub struct DaemonSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<DaemonSetSpecView>,
    pub status: Option<DaemonSetStatusView>,
}

implement_resource_view_trait!(DaemonSetView, Option<DaemonSetSpecView>, None, Option<DaemonSetStatusView>, None,
    Kind::DaemonSetKind, _state_validation, _transition_validation);


impl DaemonSetView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: DaemonSetView) -> bool {
        let old_spec = old_obj.spec->0;
        let new_spec = self.spec->0;
        old_spec.selector == new_spec.selector
    }

}


pub struct DaemonSetSpecView {
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
}

pub struct DaemonSetStatusView {
    pub number_ready: int,
}


// File: kubernetes_api_objects/spec/dynamic.rs
pub struct DynamicObjectView {
    pub kind: Kind,
    pub metadata: ObjectMetaView,
    pub spec: Value,
    pub status: Value,
}

impl DynamicObjectView {

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name is Some,
            self.metadata.namespace is Some,
    {
        ObjectRef {
            kind: self.kind,
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    pub open spec fn with_namespace(self, namespace: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                namespace: Some(namespace),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_resource_version(self, resource_version: ResourceVersion) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: Some(resource_version),
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn with_deletion_timestamp(self, deletion_timestamp: StringView) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: Some(deletion_timestamp),
                ..self.metadata
            },
            ..self
        }
    }

}



// File: kubernetes_api_objects/spec/label_selector.rs
pub struct LabelSelectorView {
    pub match_labels: Option<Map<StringView, StringView>>,
}

impl LabelSelectorView {

    pub open spec fn default() -> LabelSelectorView {
        LabelSelectorView {
            match_labels: None,
        }
    }

    pub open spec fn matches(self, labels: Map<StringView, StringView>) -> bool {
        if self.match_labels is None {
            true
        } else {
            let match_labels = self.match_labels->0;
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }

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

    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: None,
            generate_name: None,
            namespace: None,
            resource_version: None,
            uid: None,
            labels: None,
            annotations: None,
            owner_references: None,
            finalizers: None,
            deletion_timestamp: None,
        }
    }

    pub open spec fn owner_references_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs.contains(owner_ref),
            None => false,
        }
    }

    pub open spec fn finalizers_as_set(self) -> Set<StringView> {
        if self.finalizers is None {
            Set::empty()
        } else {
            self.finalizers->0.to_set()
        }
    }

    pub open spec fn well_formed_for_namespaced(self) -> bool {
        &&& self.name is Some
        &&& self.namespace is Some
        &&& self.resource_version is Some
        &&& self.uid is Some
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

pub open spec fn owner_reference_to_object_reference(owner_reference: OwnerReferenceView, namespace: StringView) -> ObjectRef {
    ObjectRef {
        kind: owner_reference.kind,
        namespace: namespace,
        name: owner_reference.name,
    }
}


// File: kubernetes_api_objects/spec/persistent_volume_claim.rs
pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
    pub status: Option<PersistentVolumeClaimStatusView>,
}

implement_resource_view_trait!(PersistentVolumeClaimView, Option<PersistentVolumeClaimSpecView>, None,
    Option<PersistentVolumeClaimStatusView>, None, Kind::PersistentVolumeClaimKind, _state_validation,
    _transition_validation);

impl PersistentVolumeClaimView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: PersistentVolumeClaimView) -> bool { true }

}


pub struct PersistentVolumeClaimSpecView {
    pub storage_class_name: Option<StringView>,
    pub access_modes: Option<Seq<StringView>>,
    pub resources: Option<VolumeResourceRequirementsView>,
}


// File: kubernetes_api_objects/spec/pod.rs
pub struct PodView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PodSpecView>,
    pub status: Option<PodStatusView>,
}

implement_resource_view_trait!(PodView, Option<PodSpecView>, None, Option<PodStatusView>, None,
    Kind::PodKind, _state_validation, _transition_validation);

impl PodView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: PodView) -> bool { true }

}


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


// File: kubernetes_api_objects/spec/role.rs
pub struct RoleView {
    pub metadata: ObjectMetaView,
    pub policy_rules: Option<Seq<PolicyRuleView>>,
}

implement_resource_view_trait!(RoleView, RoleSpecView, EmptyStatusView, _default, Kind::RoleKind, _spec, _status,
    _unmarshal_helper, _state_validation, _transition_validation);

impl RoleView {

    #[verifier(inline)]
    pub open spec fn _default() -> RoleView {
        RoleView {
            metadata: ObjectMetaView::default(),
            policy_rules: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> RoleSpecView {
        self.policy_rules
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleView {
        RoleView {
            metadata: obj.metadata,
            policy_rules: RoleView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.policy_rules is Some
            ==> (forall |i| 0 <= i < self.policy_rules->0.len() ==> #[trigger] self.policy_rules->0[i].state_validation())
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: RoleView) -> bool { true }

}


pub struct PolicyRuleView {
    pub api_groups: Option<Seq<StringView>>,
    pub resources: Option<Seq<StringView>>,
    pub verbs: Seq<StringView>,
}

impl PolicyRuleView {

    pub open spec fn state_validation(self) -> bool {
        &&& self.api_groups is Some
        &&& self.api_groups->0.len() > 0
        &&& self.resources is Some
        &&& self.resources->0.len() > 0
        &&& self.verbs.len() > 0
    }

}



// File: kubernetes_api_objects/spec/role_binding.rs
pub struct RoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

implement_resource_view_trait!(RoleBindingView, RoleBindingSpecView, EmptyStatusView, _default, Kind::RoleBindingKind,
    _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

impl RoleBindingView {

    #[verifier(inline)]
    pub open spec fn _default() -> RoleBindingView {
        RoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> RoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleBindingView {
        RoleBindingView {
            metadata: obj.metadata,
            role_ref: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.0,
            subjects: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.1,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        &&& self.role_ref.api_group == "rbac.authorization.k8s.io"@
        &&& (self.role_ref.kind == "Role"@ || self.role_ref.kind == "ClusterRole"@)
        // &&& self.role_ref.name.len() > 0
        // &&& self.subjects is Some
        //     ==> forall |i| 0 <= i < self.subjects->0.len() ==> #[trigger] self.subjects->0[i].state_validation(true)
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: RoleBindingView) -> bool {
        old_obj.role_ref == self.role_ref // role_ref is immutable
    }

}


pub struct RoleRefView {
    pub api_group: StringView,
    pub kind: StringView,
    pub name: StringView,
}

impl RoleRefView {

    pub open spec fn default() -> RoleRefView {
        RoleRefView {
            api_group: ""@,
            kind: ""@,
            name: ""@,
        }
    }

}


pub struct SubjectView {
    pub kind: StringView,
    pub name: StringView,
    pub namespace: Option<StringView>,
}


// File: kubernetes_api_objects/spec/secret.rs
pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, <String, String> map is used instead of <String, Bytestring> map for now.
}

implement_resource_view_trait!(SecretView, SecretSpecView, EmptyStatusView, _default, Kind::SecretKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);

impl SecretView {

    #[verifier(inline)]
    pub open spec fn _default() -> SecretView {
        SecretView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> SecretSpecView {
        self.data
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> SecretView {
        SecretView {
            metadata: obj.metadata,
            data: SecretView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: SecretView) -> bool { true }

}



// File: kubernetes_api_objects/spec/service.rs
pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
    pub status: Option<ServiceStatusView>,
}

implement_resource_view_trait!(ServiceView, Option<ServiceSpecView>, None, Option<ServiceStatusView>, None,
    Kind::ServiceKind, _state_validation, _transition_validation);

impl ServiceView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ServiceView) -> bool { true }

}


pub struct ServiceSpecView {
    pub cluster_ip: Option<StringView>,
    pub ports: Option<Seq<ServicePortView>>,
    pub selector: Option<Map<StringView, StringView>>,
    pub publish_not_ready_addresses: Option<bool>,
}

pub struct ServicePortView {
    pub name: Option<StringView>,
    pub port: int,
    pub app_protocol: Option<StringView>,
    pub protocol: Option<StringView>,
}


// File: kubernetes_api_objects/spec/service_account.rs
pub struct ServiceAccountView {
    pub metadata: ObjectMetaView,
    pub automount_service_account_token: Option<bool>,
}

implement_resource_view_trait!(ServiceAccountView, ServiceAccountSpecView, EmptyStatusView, _default,
    Kind::ServiceAccountKind, _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

impl ServiceAccountView {

    #[verifier(inline)]
    pub open spec fn _default() -> ServiceAccountView {
        ServiceAccountView {
            metadata: ObjectMetaView::default(),
            automount_service_account_token: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> ServiceAccountSpecView {
        self.automount_service_account_token
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: obj.metadata,
            automount_service_account_token: ServiceAccountView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ServiceAccountView) -> bool { true }

}



// File: kubernetes_api_objects/spec/stateful_set.rs
pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
    pub status: Option<StatefulSetStatusView>,
}

implement_resource_view_trait!(StatefulSetView, Option<StatefulSetSpecView>, None, Option<StatefulSetStatusView>, None,
    Kind::StatefulSetKind, _state_validation, _transition_validation);

impl StatefulSetView {

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        let new_spec = self.spec->0;
        &&& self.spec is Some
        &&& new_spec.replicas is Some ==> new_spec.replicas->0 >= 0
        // &&& new_spec.pod_management_policy is Some
        //     ==> (new_spec.pod_management_policy->0 == "OrderedReady"@
        //         || new_spec.pod_management_policy->0 == "Parallel"@)
        // &&& new_spec.persistent_volume_claim_retention_policy is Some
        //     ==> new_spec.persistent_volume_claim_retention_policy->0.state_validation()
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: StatefulSetView) -> bool {
        let old_spec = old_obj.spec->0;
        let new_spec = self.spec->0;
        // Fields other than replicas, template, persistent_volume_claim_retention_policy
        // (and some other unspecified fields) are immutable.
        &&& old_spec == StatefulSetSpecView {
            replicas: old_spec.replicas,
            template: old_spec.template,
            persistent_volume_claim_retention_policy: old_spec.persistent_volume_claim_retention_policy,
            ..new_spec
        }
    }

}


pub struct StatefulSetSpecView {
    pub min_ready_seconds: Option<int>,
    pub ordinals: Option<StatefulSetOrdinalsView>,
    pub persistent_volume_claim_retention_policy: Option<StatefulSetPersistentVolumeClaimRetentionPolicyView>,
    pub pod_management_policy: Option<StringView>,
    pub replicas: Option<int>,
    pub revision_history_limit: Option<int>,
    pub selector: LabelSelectorView,
    pub service_name: StringView,
    pub template: PodTemplateSpecView,
    pub update_strategy: Option<StatefulSetUpdateStrategyView>,
    pub volume_claim_templates: Option<Seq<PersistentVolumeClaimView>>,
}

pub struct StatefulSetPersistentVolumeClaimRetentionPolicyView {
    pub when_deleted: Option<StringView>,
    pub when_scaled: Option<StringView>,
}

pub struct StatefulSetOrdinalsView {
    pub start: Option<int>
}

pub struct StatefulSetUpdateStrategyView {
    pub type_: Option<StringView>,
    pub rolling_update: Option<RollingUpdateStatefulSetStrategyView>,
}

pub struct RollingUpdateStatefulSetStrategyView {
    pub partition: Option<int>,
    pub max_unavailable: Option<int>
}

pub struct StatefulSetStatusView {
    pub ready_replicas: Option<int>,
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


// File: kubernetes_api_objects/spec/volume_resource_requirements.rs
pub struct VolumeResourceRequirementsView {
    pub limits: Option<Map<StringView, StringView>>,
    pub requests: Option<Map<StringView, StringView>>,
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

    #[verifier(inline)]
    pub open spec fn ongoing_reconciles(self, controller_id: int) -> Map<ObjectRef, OngoingReconcile> {
        self.controller_and_externals[controller_id].controller.ongoing_reconciles
    }

}


#[is_variant]
pub enum Step {
    APIServerStep(Option<Message>),
    BuiltinControllersStep((BuiltinControllerChoice, ObjectRef)),
    ControllerStep((int, Option<Message>, Option<ObjectRef>)),
    ScheduleControllerReconcileStep((int, ObjectRef)),
    RestartControllerStep(int),
    DisableCrashStep(int),
    DropReqStep((Message, APIError)),
    DisableReqDropStep,
    PodMonkeyStep(PodView),
    DisablePodMonkeyStep,
    ExternalStep((int, Option<Message>)),
    StutterStep,
}

pub struct Cluster {
    pub installed_types: InstalledTypes,
    pub controller_models: Map<int, ControllerModel>,
}

pub struct ControllerModel {
    pub reconcile_model: ReconcileModel,
    pub external_model: Option<ExternalModel>,
}

impl Cluster {

    pub open spec fn next_step(self, s: ClusterState, s_prime: ClusterState, step: Step) -> bool {
        match step {
            Step::APIServerStep(input) => self.api_server_next().forward(input)(s, s_prime),
            Step::BuiltinControllersStep(input) => self.builtin_controllers_next().forward(input)(s, s_prime),
            Step::ControllerStep(input) => self.controller_next().forward(input)(s, s_prime),
            Step::ScheduleControllerReconcileStep(input) => self.schedule_controller_reconcile().forward(input)(s, s_prime),
            Step::RestartControllerStep(input) => self.restart_controller().forward(input)(s, s_prime),
            Step::DisableCrashStep(input) => self.disable_crash().forward(input)(s, s_prime),
            Step::DropReqStep(input) => self.drop_req().forward(input)(s, s_prime),
            Step::DisableReqDropStep => self.disable_req_drop().forward(())(s, s_prime),
            Step::PodMonkeyStep(input) => self.pod_monkey_next().forward(input)(s, s_prime),
            Step::DisablePodMonkeyStep => self.disable_pod_monkey().forward(())(s, s_prime),
            Step::ExternalStep(input) => self.external_next().forward(input)(s, s_prime),
            Step::StutterStep => self.stutter().forward(())(s, s_prime),
        }
    }

    pub open spec fn api_server_next(self) -> Action<ClusterState, Option<Message>, ()> {
        let result = |input: Option<Message>, s: ClusterState| {
            let host_result = self.api_server().next_result(
                APIServerActionInput{ recv: input },
                s.api_server
            );
            let msg_ops = MessageOps {
                recv: input,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: Option<Message>, s: ClusterState| {
                &&& received_msg_destined_for(input, HostId::APIServer)
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: Option<Message>, s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                (ClusterState {
                    api_server: host_result.get_Enabled_0(),
                    network: network_result.get_Enabled_0(),
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn builtin_controllers_next(self) -> Action<ClusterState, (BuiltinControllerChoice, ObjectRef), ()> {
        let result = |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
            let host_result = self.builtin_controllers().next_result(
                BuiltinControllersActionInput {
                    choice: input.0,
                    key: input.1,
                    rpc_id_allocator: s.rpc_id_allocator,
                    resources: s.api_server.resources,
                },
                ()
            );
            let msg_ops = MessageOps {
                recv: None,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: (BuiltinControllerChoice, ObjectRef), s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                (ClusterState {
                    network: network_result.get_Enabled_0(),
                    rpc_id_allocator: host_result.get_Enabled_1().rpc_id_allocator,
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn controller_next(self) -> Action<ClusterState, (int, Option<Message>, Option<ObjectRef>), ()> {
        Action {
            precondition: |input: (int, Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_controller_next(controller_id);
                (chosen_action.precondition)((input.1, input.2), s)
            },
            transition: |input: (int, Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_controller_next(controller_id);
                (chosen_action.transition)((input.1, input.2), s)
            },
        }
    }

    pub open spec fn chosen_controller_next(self, controller_id: int) -> Action<ClusterState, (Option<Message>, Option<ObjectRef>), ()> {
        let result = |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
            let host_result = self.controller(controller_id).next_result(
                ControllerActionInput{recv: input.0, scheduled_cr_key: input.1, rpc_id_allocator: s.rpc_id_allocator},
                s.controller_and_externals[controller_id].controller
            );
            let msg_ops = MessageOps {
                recv: input.0,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
                &&& self.controller_models.contains_key(controller_id)
                &&& input.1 is Some
                &&& received_msg_destined_for(input.0, HostId::Controller(controller_id, input.1->0))
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: (Option<Message>, Option<ObjectRef>), s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: host_result.get_Enabled_0(),
                    ..s.controller_and_externals[controller_id]
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    network: network_result.get_Enabled_0(),
                    rpc_id_allocator: host_result.get_Enabled_1().rpc_id_allocator,
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn schedule_controller_reconcile(self) -> Action<ClusterState, (int, ObjectRef), ()> {
        Action {
            precondition: |input: (int, ObjectRef), s: ClusterState| {
                let controller_id = input.0;
                let object_key = input.1;
                &&& s.resources().contains_key(object_key)
                &&& self.controller_models.contains_key(controller_id)
                &&& object_key.kind == self.controller_models[controller_id].reconcile_model.kind
            },
            transition: |input: (int, ObjectRef), s: ClusterState| {
                let controller_id = input.0;
                let object_key = input.1;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: ControllerState {
                        scheduled_reconciles: controller_and_external_state.controller.scheduled_reconciles.insert(object_key, s.resources()[object_key]),
                        ..controller_and_external_state.controller
                    },
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            }
        }
    }

    pub open spec fn restart_controller(self) -> Action<ClusterState, int, ()> {
        Action {
            precondition: |input: int, s: ClusterState| {
                let controller_id = input;
                &&& self.controller_models.contains_key(controller_id)
                &&& s.controller_and_externals[controller_id].crash_enabled
            },
            transition: |input: int, s: ClusterState| {
                let controller_id = input;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    controller: ControllerState {
                        scheduled_reconciles: Map::<ObjectRef, DynamicObjectView>::empty(),
                        ongoing_reconciles: Map::<ObjectRef, OngoingReconcile>::empty(),
                        reconcile_id_allocator: controller_and_external_state.controller.reconcile_id_allocator,
                    },
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn disable_crash(self) -> Action<ClusterState, int, ()> {
        Action {
            precondition: |input: int, s: ClusterState| {
                let controller_id = input;
                self.controller_models.contains_key(controller_id)
            },
            transition: |input: int, s: ClusterState| {
                let controller_id = input;
                let controller_and_external_state = s.controller_and_externals[controller_id];
                let controller_and_external_state_prime = ControllerAndExternalState {
                    crash_enabled: false,
                    ..controller_and_external_state
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn drop_req(self) -> Action<ClusterState, (Message, APIError), ()> {
        let result = |input: (Message, APIError), s: ClusterState| {
            let req_msg = input.0;
            let api_err = input.1;
            let resp = form_matched_err_resp_msg(req_msg, api_err);
            let msg_ops = MessageOps {
                recv: Some(req_msg),
                send: Multiset::singleton(resp),
            };
            let result = network().next_result(msg_ops, s.network);
            result
        };
        Action {
            precondition: |input: (Message, APIError), s: ClusterState| {
                let req_msg = input.0;
                let api_err = input.1;
                &&& s.req_drop_enabled
                &&& req_msg.dst.is_APIServer()
                &&& req_msg.content.is_APIRequest()
                &&& result(input, s).is_Enabled()
            },
            transition: |input: (Message, APIError), s: ClusterState| {
                (ClusterState {
                    network: result(input, s).get_Enabled_0(),
                    ..s
                }, ())
            }
        }
    }

    pub open spec fn disable_req_drop(self) -> Action<ClusterState, (), ()> {
        Action {
            precondition: |input:(), s: ClusterState| {
                true
            },
            transition: |input: (), s: ClusterState| {
                (ClusterState {
                    req_drop_enabled: false,
                    ..s
                }, ())
            }
        }
    }

    pub open spec fn pod_monkey_next(self) -> Action<ClusterState, PodView, ()> {
        let result = |input: PodView, s: ClusterState| {
            let host_result = self.pod_monkey().next_result(
                PodMonkeyActionInput{pod: input, rpc_id_allocator: s.rpc_id_allocator},
                ()
            );
            let msg_ops = MessageOps {
                recv: None,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: PodView, s: ClusterState| {
                &&& s.pod_monkey_enabled
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: PodView, s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                (ClusterState {
                    network: network_result.get_Enabled_0(),
                    rpc_id_allocator: host_result.get_Enabled_1().rpc_id_allocator,
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn disable_pod_monkey(self) -> Action<ClusterState, (), ()> {
        Action {
            precondition: |input:(), s: ClusterState| {
                true
            },
            transition: |input: (), s: ClusterState| {
                (ClusterState {
                    pod_monkey_enabled: false,
                    ..s
                }, ())
            }
        }
    }

    pub open spec fn external_next(self) -> Action<ClusterState, (int, Option<Message>), ()> {
        Action {
            precondition: |input: (int, Option<Message>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_external_next(controller_id);
                (chosen_action.precondition)((input.1), s)
            },
            transition: |input: (int, Option<Message>), s: ClusterState| {
                let controller_id = input.0;
                let chosen_action = self.chosen_external_next(controller_id);
                (chosen_action.transition)((input.1), s)
            },
        }
    }

    pub open spec fn chosen_external_next(self, controller_id: int) -> Action<ClusterState, Option<Message>, ()> {
        let result = |input: Option<Message>, s: ClusterState| {
            let host_result = self.external(controller_id).next_result(
                ExternalActionInput{recv: input, resources: s.api_server.resources},
                s.controller_and_externals[controller_id].external->0
            );
            let msg_ops = MessageOps {
                recv: input,
                send: host_result.get_Enabled_1().send,
            };
            let network_result = network().next_result(msg_ops, s.network);

            (host_result, network_result)
        };
        Action {
            precondition: |input: Option<Message>, s: ClusterState| {
                &&& self.controller_models.contains_key(controller_id)
                &&& self.controller_models[controller_id].external_model is Some
                &&& received_msg_destined_for(input, HostId::External(controller_id))
                &&& result(input, s).0.is_Enabled()
                &&& result(input, s).1.is_Enabled()
            },
            transition: |input: Option<Message>, s: ClusterState| {
                let (host_result, network_result) = result(input, s);
                let controller_and_external_state_prime = ControllerAndExternalState {
                    external: Some(host_result.get_Enabled_0()),
                    ..s.controller_and_externals[controller_id]
                };
                (ClusterState {
                    controller_and_externals: s.controller_and_externals.insert(controller_id, controller_and_external_state_prime),
                    network: network_result.get_Enabled_0(),
                    ..s
                }, ())
            },
        }
    }

    pub open spec fn stutter(self) -> Action<ClusterState, (), ()> {
        Action {
            precondition: |input: (), s: ClusterState| {
                true
            },
            transition: |input: (), s: ClusterState| {
                (s, ())
            },
        }
    }

    pub open spec fn api_server(self) -> APIServerStateMachine {
        api_server(self.installed_types)
    }

    pub open spec fn builtin_controllers(self) -> BuiltinControllersStateMachine {
        builtin_controllers()
    }

    pub open spec fn controller(self, controller_id: int) -> ControllerStateMachine {
        controller(self.controller_models[controller_id].reconcile_model, controller_id)
    }

    pub open spec fn pod_monkey(self) -> PodMonkeyStateMachine {
        pod_monkey()
    }

    pub open spec fn external(self, controller_id: int) -> ExternalStateMachine {
        external(self.controller_models[controller_id].external_model->0)
    }

}



// File: kubernetes_cluster/spec/message.rs
pub struct MessageOps {
    pub recv: Option<Message>,
    pub send: Multiset<Message>,
}

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

impl RPCIdAllocator {

    pub open spec fn allocate(self) -> (Self, RPCId) {
        (RPCIdAllocator {
            rpc_id_counter: self.rpc_id_counter + 1,
        }, self.rpc_id_counter)
    }

}


#[is_variant]
pub enum MessageContent {
    APIRequest(APIRequest),
    APIResponse(APIResponse),
    ExternalRequest(ExternalRequest),
    ExternalResponse(ExternalResponse),
}

pub open spec fn controller_req_msg(controller_id: int, cr_key: ObjectRef, req_id: RPCId, req: APIRequest) -> Message {
    form_msg(HostId::Controller(controller_id, cr_key), HostId::APIServer, req_id, MessageContent::APIRequest(req))
}

pub open spec fn controller_external_req_msg(controller_id: int, cr_key: ObjectRef, req_id: RPCId, req: ExternalRequest) -> Message {
    form_msg(HostId::Controller(controller_id, cr_key), HostId::External(controller_id), req_id, MessageContent::ExternalRequest(req))
}

pub open spec fn built_in_controller_req_msg(rpc_id: RPCId, msg_content: MessageContent) -> Message {
    form_msg(HostId::BuiltinController, HostId::APIServer, rpc_id, msg_content)
}

pub open spec fn pod_monkey_req_msg(rpc_id: RPCId, msg_content: MessageContent) -> Message {
    form_msg(HostId::PodMonkey, HostId::APIServer, rpc_id, msg_content)
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

pub open spec fn form_matched_err_resp_msg(req_msg: Message, err: APIError) -> Message
    recommends req_msg.content.is_APIRequest(),
{
    match req_msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => form_get_resp_msg(req_msg, GetResponse{res: Err(err)}),
        APIRequest::ListRequest(_) => form_list_resp_msg(req_msg, ListResponse{res: Err(err)}),
        APIRequest::CreateRequest(_) => form_create_resp_msg(req_msg, CreateResponse{res: Err(err)}),
        APIRequest::DeleteRequest(_) => form_delete_resp_msg(req_msg, DeleteResponse{res: Err(err)}),
        APIRequest::UpdateRequest(_) => form_update_resp_msg(req_msg, UpdateResponse{res: Err(err)}),
        APIRequest::UpdateStatusRequest(_) => form_update_status_resp_msg(req_msg, UpdateStatusResponse{res: Err(err)}),
        APIRequest::GetThenDeleteRequest(_) => form_get_then_delete_resp_msg(req_msg, GetThenDeleteResponse{res: Err(err)}),
        APIRequest::GetThenUpdateRequest(_) => form_get_then_update_resp_msg(req_msg, GetThenUpdateResponse{res: Err(err)}),
    }
}

pub open spec fn form_msg(src: HostId, dst: HostId, rpc_id: RPCId, msg_content: MessageContent) -> Message {
    Message {
        src: src,
        dst: dst,
        rpc_id: rpc_id,
        content: msg_content,
    }
}

pub open spec fn form_external_resp_msg(req_msg: Message, resp: ExternalResponse) -> Message
    recommends req_msg.content.is_ExternalRequest(),
{
    form_msg(req_msg.dst, req_msg.src, req_msg.rpc_id, MessageContent::ExternalResponse(resp))
}

pub open spec fn create_req_msg_content(namespace: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::CreateRequest(CreateRequest{
        namespace: namespace,
        obj: obj,
    }))
}

pub open spec fn delete_req_msg_content(key: ObjectRef, preconditions: Option<PreconditionsView>) -> MessageContent {
    MessageContent::APIRequest(APIRequest::DeleteRequest(DeleteRequest{
        key: key,
        preconditions: preconditions,
    }))
}

pub open spec fn update_req_msg_content(namespace: StringView, name: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::UpdateRequest(UpdateRequest{
        namespace: namespace,
        name: name,
        obj: obj,
    }))
}

pub open spec fn update_status_req_msg_content(namespace: StringView, name: StringView, obj: DynamicObjectView) -> MessageContent {
    MessageContent::APIRequest(APIRequest::UpdateStatusRequest(UpdateStatusRequest{
        namespace: namespace,
        name: name,
        obj: obj,
    }))
}

pub open spec fn received_msg_destined_for(recv: Option<Message>, host_id: HostId) -> bool {
    if recv is Some {
        recv->0.dst == host_id
    } else {
        true
    }
}

macro_rules! declare_message_content_req_helper_methods {
    ($is_fun:ident, $get_fun:ident, $req_type:ty, $project:ident) => {
        verus! {

        impl MessageContent {

            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIRequest
                &&& self.get_APIRequest_0() is $req_type
            }

            pub open spec fn $get_fun(self) -> $req_type {
                self.get_APIRequest_0().$project()
            }
        }
        }
    };

}

declare_message_content_req_helper_methods!(
    is_get_request,
    get_get_request,
    GetRequest,
    get_GetRequest_0
);

declare_message_content_req_helper_methods!(
    is_list_request,
    get_list_request,
    ListRequest,
    get_ListRequest_0
);

declare_message_content_req_helper_methods!(
    is_create_request,
    get_create_request,
    CreateRequest,
    get_CreateRequest_0
);

declare_message_content_req_helper_methods!(
    is_delete_request,
    get_delete_request,
    DeleteRequest,
    get_DeleteRequest_0
);

declare_message_content_req_helper_methods!(
    is_update_status_request,
    get_update_status_request,
    UpdateStatusRequest,
    get_UpdateStatusRequest_0
);

declare_message_content_req_helper_methods!(
    is_update_request,
    get_update_request,
    UpdateRequest,
    get_UpdateRequest_0
);

declare_message_content_req_helper_methods!(
    is_get_then_delete_request,
    get_get_then_delete_request,
    GetThenDeleteRequest,
    get_GetThenDeleteRequest_0
);

declare_message_content_req_helper_methods!(
    is_get_then_update_request,
    get_get_then_update_request,
    GetThenUpdateRequest,
    get_GetThenUpdateRequest_0
);

macro_rules! declare_message_content_resp_helper_methods {
    ($is_fun:ident, $get_fun:ident, $resp_type:ty, $project:ident) => {
        verus! {
        impl MessageContent {
            pub open spec fn $is_fun(self) -> bool {
                &&& self is APIResponse
                &&& self.get_APIResponse_0() is $resp_type
            }

            pub open spec fn $get_fun(self) -> $resp_type {
                self.get_APIResponse_0().$project()
            }
        }
        }
    };
}

declare_message_content_resp_helper_methods!(
    is_get_then_delete_response,
    get_get_then_delete_response,
    GetThenDeleteResponse,
    get_GetThenDeleteResponse_0
);


declare_message_content_resp_helper_methods!(
    is_update_status_response,
    get_update_status_response,
    UpdateStatusResponse,
    get_UpdateStatusResponse_0
);

declare_message_content_resp_helper_methods!(
    is_list_response,
    get_list_response,
    ListResponse,
    get_ListResponse_0
);

macro_rules! declare_form_resp_msg_functions {
    ($fun:ident, $resp_type:ty) => {
        verus! {
        pub open spec fn $fun(req_msg: Message, resp: $resp_type) -> Message {
            form_msg(req_msg.dst, req_msg.src, req_msg.rpc_id, MessageContent::APIResponse(APIResponse::$resp_type(resp)))
        }
        }
    };
}

declare_form_resp_msg_functions!(form_get_resp_msg, GetResponse);

declare_form_resp_msg_functions!(form_list_resp_msg, ListResponse);

declare_form_resp_msg_functions!(form_create_resp_msg, CreateResponse);

declare_form_resp_msg_functions!(form_delete_resp_msg, DeleteResponse);

declare_form_resp_msg_functions!(form_update_resp_msg, UpdateResponse);

declare_form_resp_msg_functions!(form_update_status_resp_msg, UpdateStatusResponse);

declare_form_resp_msg_functions!(form_get_then_delete_resp_msg, GetThenDeleteResponse);

declare_form_resp_msg_functions!(form_get_then_update_resp_msg, GetThenUpdateResponse);

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

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        // replicas is non-negative
        &&& self.spec.replicas is Some ==> self.spec.replicas->0 >= 0
        // selector exists, and its match_labels is not empty
        // TODO: revise it after supporting selector.match_expressions
        &&& self.spec.selector.match_labels is Some
        // labels are finite
        &&& self.spec.selector.match_labels->0.dom().finite()
        &&& self.spec.selector.match_labels->0.len() > 0
        // template, and its metadata ane spec exists
        &&& self.spec.template is Some
        &&& self.spec.template->0.metadata is Some
        &&& self.spec.template->0.spec is Some
        // kubernetes requires selector matches template's metadata's labels
        // and also requires selector to be non-empty, so it implicitly requires that the labels are non-empty
        &&& self.spec.template->0.metadata->0.labels is Some
        &&& self.spec.template->0.metadata->0.labels->0.dom().finite()
        &&& self.spec.selector.matches(self.spec.template->0.metadata->0.labels->0)
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: VReplicaSetView) -> bool {
        true
    }

}


pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}

impl VReplicaSetSpecView {

    pub open spec fn default() -> VReplicaSetSpecView {
        VReplicaSetSpecView {
            replicas: None,
            selector: LabelSelectorView::default(),
            template: None,
        }
    }

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


// File: state_machine/state_machine.rs
#[verifier(reject_recursive_types(State))]
#[verifier(reject_recursive_types(Step))]
#[verifier(reject_recursive_types(Output))]
#[verifier(reject_recursive_types(ActionInput))]
#[verifier(reject_recursive_types(Input))]
pub struct StateMachine <State, Input, ActionInput, Output, Step> {
    // Check if it is the initial internal state.
    pub init: spec_fn(State) -> bool,

    // The set of actions the state machine can take.
    pub actions: Set<Action<State, ActionInput, Output>>,

    // Return the corresponding action of the binding step.
    pub step_to_action: spec_fn(Step) -> Action<State, ActionInput, Output>,

    // Return the input to the host action.
    pub action_input: spec_fn(Step, Input) -> ActionInput,
}

impl<State, Input, ActionInput, Output, Step> StateMachine<State, Input, ActionInput, Output, Step> {

    pub open spec fn next_result(self, input: Input, s: State) -> ActionResult<State, Output> {
        if exists |step| (#[trigger] (self.step_to_action)(step).precondition)((self.action_input)(step, input), s) {
            let witness_step = choose |step| (#[trigger] (self.step_to_action)(step).precondition)((self.action_input)(step, input), s);
            let action = (self.step_to_action)(witness_step);
            let action_input = (self.action_input)(witness_step, input);
            ActionResult::Enabled((action.transition)(action_input, s).0, (action.transition)(action_input, s).1)
        } else {
            ActionResult::Disabled
        }
    }

}


#[verifier(reject_recursive_types(MessageOps))]
#[verifier(reject_recursive_types(State))]
pub struct NetworkStateMachine <State, MessageOps> {
    // Check if it is the initial internal state.
    pub init: spec_fn(State) -> bool,

    // The deliver action that (1) sends zero or one message to a host and (2) takes any number of messages from a host.
    pub deliver: Action<State, MessageOps, ()>,
}

impl<State, MessageOps> NetworkStateMachine<State, MessageOps> {

    pub open spec fn next_result(self, msg_ops: MessageOps, s: State) -> ActionResult<State, ()> {
        if (self.deliver.precondition)(msg_ops, s) {
            ActionResult::Enabled((self.deliver.transition)(msg_ops, s).0, (self.deliver.transition)(msg_ops, s).1)
        } else {
            ActionResult::Disabled
        }
    }

}



// File: state_machine/action.rs
#[verifier(reject_recursive_types(Output))]
#[verifier(reject_recursive_types(Input))]
#[verifier(reject_recursive_types(State))]
pub struct Action<State, Input, Output> {
    // The condition that enables the host action.
    pub precondition: spec_fn(Input, State) -> bool,

    // The new internal state and output made by the transition.
    pub transition: spec_fn(Input, State) -> (State, Output),
}

impl<State, Input, Output> Action<State, Input, Output> {

    pub open spec fn forward(self, input: Input) -> ActionPred<State> {
        |s: State, s_prime: State| {
            &&& (self.precondition)(input, s)
            &&& s_prime == (self.transition)(input, s).0
        }
    }

}


#[is_variant]
pub enum ActionResult<State, Output> {
    Disabled,
    Enabled(State, Output)
}


// File: kubernetes_cluster/spec/api_server/state_machine.rs
#[verifier(inline)]
pub open spec fn unmarshallable_spec(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_spec(obj.spec) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_spec(obj.spec) is Ok,
        Kind::PodKind => PodView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleKind => RoleView::unmarshal_spec(obj.spec) is Ok,
        Kind::SecretKind => SecretView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_spec(obj.spec) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_spec(obj.spec) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_spec)(obj.spec),
    }
}

#[verifier(inline)]
pub open spec fn unmarshallable_status(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_status(obj.status) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_status(obj.status) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_status(obj.status) is Ok,
        Kind::PodKind => PodView::unmarshal_status(obj.status) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_status(obj.status) is Ok,
        Kind::RoleKind => RoleView::unmarshal_status(obj.status) is Ok,
        Kind::SecretKind => SecretView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_status(obj.status) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_status(obj.status) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_status)(obj.status),
    }
}

pub open spec fn unmarshallable_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    unmarshallable_spec(obj, installed_types) && unmarshallable_status(obj, installed_types)
}

pub open spec fn metadata_validity_check(obj: DynamicObjectView) -> Option<APIError> {
    if obj.metadata.owner_references is Some
    && obj.metadata.owner_references->0.len() > 1
    && obj.metadata.owner_references->0.filter(|o: OwnerReferenceView| o.controller is Some && o.controller->0).len() > 1 {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn metadata_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if old_obj.metadata.deletion_timestamp is Some
    && obj.metadata.finalizers is Some // Short circuit: we don't need to reason about the set difference if the finalizers is None
    && !obj.metadata.finalizers_as_set().subset_of(old_obj.metadata.finalizers_as_set()) {
        Some(APIError::Forbidden)
    } else {
        None
    }
}

pub open spec fn valid_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PodKind => PodView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleKind => RoleView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::SecretKind => SecretView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceKind => ServiceView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::CustomResourceKind(string) => (installed_types[string].valid_object)(obj),
    }
}

pub open spec fn object_validity_check(obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if !valid_object(obj, installed_types) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn valid_transition(obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj)->Ok_0.transition_validation(ConfigMapView::unmarshal(old_obj)->Ok_0),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj)->Ok_0.transition_validation(DaemonSetView::unmarshal(old_obj)->Ok_0),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj)->Ok_0.transition_validation(PersistentVolumeClaimView::unmarshal(old_obj)->Ok_0),
        Kind::PodKind => PodView::unmarshal(obj)->Ok_0.transition_validation(PodView::unmarshal(old_obj)->Ok_0),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj)->Ok_0.transition_validation(RoleBindingView::unmarshal(old_obj)->Ok_0),
        Kind::RoleKind => RoleView::unmarshal(obj)->Ok_0.transition_validation(RoleView::unmarshal(old_obj)->Ok_0),
        Kind::SecretKind => SecretView::unmarshal(obj)->Ok_0.transition_validation(SecretView::unmarshal(old_obj)->Ok_0),
        Kind::ServiceKind => ServiceView::unmarshal(obj)->Ok_0.transition_validation(ServiceView::unmarshal(old_obj)->Ok_0),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj)->Ok_0.transition_validation(StatefulSetView::unmarshal(old_obj)->Ok_0),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj)->Ok_0.transition_validation(ServiceAccountView::unmarshal(old_obj)->Ok_0),
        Kind::CustomResourceKind(string) => (installed_types[string].valid_transition)(obj, old_obj),
    }
}

pub open spec fn object_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if !valid_transition(obj, old_obj, installed_types) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn marshalled_default_status(kind: Kind, installed_types: InstalledTypes) -> Value {
    match kind {
        Kind::ConfigMapKind => ConfigMapView::marshal_status(ConfigMapView::default().status()),
        Kind::DaemonSetKind => DaemonSetView::marshal_status(DaemonSetView::default().status()),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::marshal_status(PersistentVolumeClaimView::default().status()),
        Kind::PodKind => PodView::marshal_status(PodView::default().status()),
        Kind::RoleBindingKind => RoleBindingView::marshal_status(RoleBindingView::default().status()),
        Kind::RoleKind => RoleView::marshal_status(RoleView::default().status()),
        Kind::SecretKind => SecretView::marshal_status(SecretView::default().status()),
        Kind::ServiceKind => ServiceView::marshal_status(ServiceView::default().status()),
        Kind::StatefulSetKind => StatefulSetView::marshal_status(StatefulSetView::default().status()),
        Kind::ServiceAccountKind => ServiceAccountView::marshal_status(ServiceAccountView::default().status()),
        Kind::CustomResourceKind(string) => (installed_types[string].marshalled_default_status)(),
    }
}

#[verifier(inline)]
pub open spec fn handle_get_request(req: GetRequest, s: APIServerState) -> GetResponse {
    if !s.resources.contains_key(req.key) {
        // Get fails
        GetResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        // Get succeeds
        GetResponse{res: Ok(s.resources[req.key])}
    }
}

#[verifier(inline)]
pub open spec fn handle_list_request(req: ListRequest, s: APIServerState) -> ListResponse {
    // s.resources.values() returns the set of objects in s.resources
    // This will not make list return fewer number of objects because
    // each object is unique in terms of {name, namespace, kind}
    ListResponse{res: Ok(s.resources.values().filter(|o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    }).to_seq())}
}

pub open spec fn create_request_admission_check(installed_types: InstalledTypes, req: CreateRequest, s: APIServerState) -> Option<APIError> {
    if req.obj.metadata.name is None && req.obj.metadata.generate_name is None {
        // Creation fails because neither the name nor the generate_name of the provided object is provided
        Some(APIError::Invalid)
    } else if req.obj.metadata.namespace is Some && req.namespace != req.obj.metadata.namespace->0 {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !unmarshallable_object(req.obj, installed_types) {
        // Creation fails because the provided object is not well formed
        Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if req.obj.metadata.name is Some && s.resources.contains_key(req.obj.with_namespace(req.namespace).object_ref()) {
        // Creation fails because the object has a name and it already exists
        Some(APIError::ObjectAlreadyExists)
    } else {
        None
    }
}

pub open spec fn created_object_validity_check(created_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if metadata_validity_check(created_obj) is Some {
        metadata_validity_check(created_obj)
    } else if object_validity_check(created_obj, installed_types) is Some {
        object_validity_check(created_obj, installed_types)
    } else {
        None
    }
}

pub uninterp spec fn generate_name(s: APIServerState) -> StringView;

#[verifier(inline)]
pub open spec fn handle_create_request(installed_types: InstalledTypes, req: CreateRequest, s: APIServerState) -> (APIServerState, CreateResponse) {
    if create_request_admission_check(installed_types, req, s) is Some {
        // Creation fails.
        (s, CreateResponse{res: Err(create_request_admission_check(installed_types, req, s)->0)})
    } else {
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_is_unique.
                name: if req.obj.metadata.name is Some {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.resource_version_counter), // Set rv for new object
                uid: Some(s.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(req.obj.kind, installed_types), // Overwrite the status with the default one
        };
        if s.resources.contains_key(created_obj.object_ref()) {
            // Note 1: You might find this branch redundant since we already have
            // generated_name_is_unique which guarantees that the created_obj's
            // key is different from any existing keys even if name was not provided.
            // But we still add this branch just to avoid calling generated_name_is_unique
            // when we want to show that create without a provided name does not override
            // an existing object when writing proofs.
            //
            // Note 2: Adding this branch also means that if we want to prove the object
            // is eventually created by a create request without the name provided,
            // we need to explicitly call generated_name_is_unique to show that
            // we do not fall into this branch.
            (s, CreateResponse{res: Err(APIError::ObjectAlreadyExists)})
        } else if created_object_validity_check(created_obj, installed_types) is Some {
            // Creation fails.
            (s, CreateResponse{res: Err(created_object_validity_check(created_obj, installed_types)->0)})
        } else {
            // Creation succeeds.
            (APIServerState {
                resources: s.resources.insert(created_obj.object_ref(), created_obj),
                uid_counter: s.uid_counter + 1,
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, CreateResponse{res: Ok(created_obj)})
        }
    }
}

pub open spec fn delete_request_admission_check(req: DeleteRequest, s: APIServerState) -> Option<APIError> {
    if !s.resources.contains_key(req.key) {
        // Deletion fails because the object does not exist
        Some(APIError::ObjectNotFound)
    } else if req.preconditions is Some {
        let preconditions = req.preconditions->0;
        if preconditions.uid is Some && preconditions.uid != s.resources[req.key].metadata.uid {
            // Deletion fails because the uid of the object does not match the uid in the precondition
            Some(APIError::Conflict)
        } else if preconditions.resource_version is Some && preconditions.resource_version != s.resources[req.key].metadata.resource_version {
            // Deletion fails because the resource version of the object does not match the resource version in the precondition
            Some(APIError::Conflict)
        } else {
            None
        }
    } else {
        None
    }
}

pub uninterp spec fn deletion_timestamp() -> StringView;

pub open spec fn handle_delete_request(req: DeleteRequest, s: APIServerState) -> (APIServerState, DeleteResponse) {
    if delete_request_admission_check(req, s) is Some {
        // Deletion fails.
        (s, DeleteResponse{res: Err(delete_request_admission_check(req, s)->0)})
    } else {
        // Deletion succeeds.
        let obj = s.resources[req.key];
        if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
            // With the finalizer(s) in the object, we cannot immediately delete it from the key-value store.
            // Instead, we set the deletion timestamp of this object.
            // If the object already has a deletion timestamp, then skip.
            //
            // NOTE: Having finalizer(s) is not the only reason that a deletion is postponed. Having a graceful
            // period set in the deletion option is another reason. Currently we do not model the graceful period
            // option so we don't model how the API server checks whether a deletion should be graceful.
            // However, even without a graceful period option, deleting a Pod can still be graceful depending on its
            // spec content (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/apis/core/types.go#L3256)
            // because Pod implements CheckGracefulDelete (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/pod/strategy.go#L168).
            // This is irrelevant to application controllers that do not manage pods, and acceptable for verifying
            // low-level built-in controllers because they are supposed to treat terminating pods as non-existing pods.
            if obj.metadata.deletion_timestamp is Some {
                // A deletion timestamp is already set so no need to bother it.
                (s, DeleteResponse{res: Ok(())})
            } else {
                let stamped_obj_with_new_rv = obj.with_deletion_timestamp(deletion_timestamp())
                                                 .with_resource_version(s.resource_version_counter);
                (APIServerState {
                    // Here we use req.key, instead of stamped_obj.object_ref(), to insert to the map.
                    // This is intended because using stamped_obj.object_ref() will require us to use
                    // the invariant each_object_in_etcd_is_well_formed a lot more frequently:
                    // we need this invariant to convince Verus that the stamped_obj is well formed
                    // so the key we use to insert to the map is the same as req.key.
                    resources: s.resources.insert(req.key, stamped_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1,
                    ..s
                }, DeleteResponse{res: Ok(())})
            }
        } else {
            // The object can be immediately removed from the key-value store.
            //
            // NOTE: In some very corner case, the API server *seems* to first updates the object (to update its finalizers)
            // and then deletes the object immediately, which makes the entire Delete operation not atomic.
            // However, this only happens in the orphan or foreground deletion mode, so we do not model this
            // seemingly non-atomic behavior for now.
            // For more details, see how the API server updates the object in the middle of handling deletion requests:
            // https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1009
            (APIServerState {
                resources: s.resources.remove(req.key),
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, DeleteResponse{res: Ok(())})
        }
    }
}

pub open spec fn allow_unconditional_update(kind: Kind) -> bool {
    match kind {
        Kind::CustomResourceKind(_) => false,
        _ => true,
    }
}

pub open spec fn update_request_admission_check_helper(installed_types: InstalledTypes, name: StringView, namespace: StringView, obj: DynamicObjectView, s: APIServerState) -> Option<APIError> {
    let key = ObjectRef {
        kind: obj.kind,
        namespace: namespace,
        name: name,
    };
    if obj.metadata.name is None {
        // Update fails because the name of the object is not provided
        Some(APIError::BadRequest)
    } else if name != obj.metadata.name->0 {
        // Update fails because the name of the provided object
        // does not match the name sent on the request
        Some(APIError::BadRequest)
    } else if obj.metadata.namespace is Some
        && namespace != obj.metadata.namespace->0 {
        // Update fails because the namespace of the provided object
        // does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !unmarshallable_object(obj, installed_types) {
        // Update fails because the provided object is not well formed
        // TODO: should the error be BadRequest?
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(key) {
        // Update fails because the object does not exist
        // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
        Some(APIError::ObjectNotFound)
    } else if obj.metadata.resource_version is None
        && !allow_unconditional_update(key.kind) {
        // Update fails because the object does not provide a rv and unconditional update is not supported
        Some(APIError::Invalid)
    } else if obj.metadata.resource_version is Some
        && obj.metadata.resource_version != s.resources[key].metadata.resource_version {
        // Update fails because the object has a wrong rv
        Some(APIError::Conflict)
    } else if obj.metadata.uid is Some
        && obj.metadata.uid != s.resources[key].metadata.uid {
        // Update fails because the object has a wrong uid
        Some(APIError::Conflict)
    } else {
        None
    }
}

pub open spec fn update_request_admission_check(installed_types: InstalledTypes, req: UpdateRequest, s: APIServerState) -> Option<APIError> {
    update_request_admission_check_helper(installed_types, req.name, req.namespace, req.obj, s)
}

pub open spec fn updated_object(req: UpdateRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let updated_obj = DynamicObjectView {
        kind: req.obj.kind,
        metadata: ObjectMetaView {
            namespace: Some(req.namespace), // Overwrite namespace since it might not be provided
            resource_version: old_obj.metadata.resource_version, // Overwrite rv since it might not be provided
            uid: old_obj.metadata.uid, // Overwrite uid since it might not be provided
            deletion_timestamp: old_obj.metadata.deletion_timestamp, // Ignore any change to deletion_timestamp
            ..req.obj.metadata
        },
        spec: req.obj.spec,
        status: old_obj.status, // Ignore any change to status
    };
    updated_obj
}

pub open spec fn updated_object_validity_check(updated_obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if metadata_validity_check(updated_obj) is Some {
        metadata_validity_check(updated_obj)
    } else if metadata_transition_validity_check(updated_obj, old_obj) is Some {
        metadata_transition_validity_check(updated_obj, old_obj)
    } else if object_validity_check(updated_obj, installed_types) is Some {
        object_validity_check(updated_obj, installed_types)
    } else if object_transition_validity_check(updated_obj, old_obj, installed_types) is Some {
        object_transition_validity_check(updated_obj, old_obj, installed_types)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_update_request(installed_types: InstalledTypes, req: UpdateRequest, s: APIServerState) -> (APIServerState, UpdateResponse) {
    if update_request_admission_check(installed_types, req, s) is Some {
        // Update fails.
        (s, UpdateResponse{res: Err(update_request_admission_check(installed_types, req, s)->0)})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = updated_object(req, old_obj);
        if updated_obj == old_obj {
            // Update is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateResponse{res: Ok(old_obj)})
        } else {
            // Update changes something in the object (either in spec or metadata), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types) is Some {
                // Update fails.
                (s, UpdateResponse{res: Err(updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types)->0)})
            } else {
                // Update succeeds.
                if updated_obj_with_new_rv.metadata.deletion_timestamp is None
                    || (updated_obj_with_new_rv.metadata.finalizers is Some
                        && updated_obj_with_new_rv.metadata.finalizers->0.len() > 0)
                {
                    // The regular update case, where the object has no deletion timestamp set
                    // or has at least one finalizer.
                    (APIServerState {
                        resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
                } else {
                    // The delete-during-update case, where the update removes the finalizers from
                    // the object that has a deletion timestamp, so the object needs to be deleted now.
                    //
                    // NOTE: in the actual implementation, when handling an update request,
                    // the API server first applies the update to the object in the key-value store,
                    // then checks whether the object can be deleted.
                    // If so, it continues to delete the object from the key-value store before replying
                    // to the update request.
                    // This means that there is a super short window where the object has been updated in the store
                    // (with a deletion timestamp and without any finalizer), but has not been deleted yet.
                    // This behavior, strictly speaking, makes the entire Update operation not atomic.
                    // We choose to still model the Update operation as an atomic step for simplicity.
                    // This design choice does not affect the correctness of the controller that issues Update
                    // in a blocking manner because the controller will never observe this intermediate state between
                    // the update and deletion.
                    // More generally speaking, this modeling won't affect the correctness of any controller that
                    // treats a terminating object without finalizers as a non-existing object --- a good practice
                    // controllers should follow.
                    //
                    // NOTE: the API server should also check whether the deletion grace period in the metadata
                    // is set to 0 before deleting the object in case of graceful deletion
                    // (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L533).
                    // Here we omit that condition because graceful deletion is not supported.
                    (APIServerState {
                        resources: s.resources.remove(updated_obj_with_new_rv.object_ref()),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
                }
            }
        }
    }
}

pub open spec fn update_status_request_admission_check(installed_types: InstalledTypes, req: UpdateStatusRequest, s: APIServerState) -> Option<APIError> {
    update_request_admission_check_helper(installed_types, req.name, req.namespace, req.obj, s)
}

pub open spec fn status_updated_object(req: UpdateStatusRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let status_updated_object = DynamicObjectView {
        kind: req.obj.kind,
        metadata: old_obj.metadata, // Ignore any change to metadata
        spec: old_obj.spec, // Ignore any change to spec
        status: req.obj.status,
    };
    status_updated_object
}

#[verifier(inline)]
pub open spec fn handle_update_status_request(installed_types: InstalledTypes, req: UpdateStatusRequest, s: APIServerState) -> (APIServerState, UpdateStatusResponse) {
    if update_status_request_admission_check(installed_types, req, s) is Some {
        // UpdateStatus fails.
        (s, UpdateStatusResponse{res: Err(update_status_request_admission_check(installed_types, req, s)->0)})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = status_updated_object(req, old_obj);
        if updated_obj == old_obj {
            // UpdateStatus is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateStatusResponse{res: Ok(old_obj)})
        } else {
            // UpdateStatus changes something in the object (in status), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types) is Some {
                // UpdateStatus fails.
                (s, UpdateStatusResponse{res: Err(updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types)->0)})
            } else {
                // UpdateStatus succeeds.
                (APIServerState {
                    resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, UpdateStatusResponse{res: Ok(updated_obj_with_new_rv)})
            }
        }
    }
}

pub open spec fn handle_get_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    (s, form_get_resp_msg(msg, handle_get_request(req, s)))
}

pub open spec fn handle_list_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    (s, form_list_resp_msg(msg, handle_list_request(req, s)))
}

pub open spec fn handle_create_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    let (s_prime, resp) = handle_create_request(installed_types, req, s);
    (s_prime, form_create_resp_msg(msg, resp))
}

pub open spec fn handle_delete_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    let (s_prime, resp) = handle_delete_request(req, s);
    (s_prime, form_delete_resp_msg(msg, resp))
}

pub open spec fn handle_update_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    let (s_prime, resp) = handle_update_request(installed_types, req, s);
    (s_prime, form_update_resp_msg(msg, resp))
}

pub open spec fn handle_update_status_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_update_status_request(),
{
    let req = msg.content.get_update_status_request();
    let (s_prime, resp) = handle_update_status_request(installed_types, req, s);
    (s_prime, form_update_status_resp_msg(msg, resp))
}

pub open spec fn handle_get_then_delete_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_then_delete_request(),
{
    let req = msg.content.get_get_then_delete_request();
    // Step 1: get the object
    let get_req = GetRequest {
        key: req.key
    };
    let get_resp = handle_get_request(get_req, s);
    match get_resp.res {
        Ok(_) => {
            let current_obj = s.resources[req.key()];
            // Step 2: if the object exists, perform a check using a predicate on object
            // The predicate: Is the current object owned by req.owner_ref?
            // TODO: the predicate should be provided by clients instead of the hardcoded one
            if current_obj.metadata.owner_references_contains(req.owner_ref) {
                // Step 3: if the check passes, delete the object
                let delete_req = DeleteRequest {
                    key: req.key,
                    preconditions: None,
                };
                let (s_prime, delete_resp) = handle_delete_request(delete_req, s);
                (s_prime, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: delete_resp.res}))
            } else {
                (s, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: Err(APIError::TransactionAbort)}))
            }
        }
        Err(err) => (s, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: Err(err)}))
    }
}

pub open spec fn handle_get_then_update_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_then_update_request(),
{
    let req = msg.content.get_get_then_update_request();
    // Step 1: get the object
    let get_req = GetRequest {
        key: req.key()
    };
    let get_resp = handle_get_request(get_req, s);
    match get_resp.res {
        Ok(_) => {
            let current_obj = s.resources[req.key()];
            // Step 2: if the object exists, perform a check using a predicate on object
            // The predicate: Is the current object owned by req.owner_ref?
            // TODO: the predicate should be provided by clients instead of the hardcoded one
            if current_obj.metadata.owner_references_contains(req.owner_ref) {
                // Step 3: if the check passes, overwrite the object with the new one
                // Note that resource_version and uid comes from the current object to avoid conflict error
                let new_obj = DynamicObjectView {
                    metadata: ObjectMetaView {
                        resource_version: current_obj.metadata.resource_version,
                        uid: current_obj.metadata.uid,
                        ..req.obj.metadata
                    },
                    ..req.obj
                };
                let update_req = UpdateRequest {
                    name: req.name,
                    namespace: req.namespace,
                    obj: new_obj,
                };
                let (s_prime, update_resp) = handle_update_request(installed_types, update_req, s);
                (s_prime, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: update_resp.res}))
            } else {
                (s, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: Err(APIError::TransactionAbort)}))
            }
        }
        Err(err) => (s, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: Err(err)}))
    }
}

pub open spec fn transition_by_etcd(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_APIRequest(),
{
    match msg.content.get_APIRequest_0() {
        APIRequest::GetRequest(_) => handle_get_request_msg(msg, s),
        APIRequest::ListRequest(_) => handle_list_request_msg(msg, s),
        APIRequest::CreateRequest(_) => handle_create_request_msg(installed_types, msg, s),
        APIRequest::DeleteRequest(_) => handle_delete_request_msg(msg, s),
        APIRequest::UpdateRequest(_) => handle_update_request_msg(installed_types, msg, s),
        APIRequest::UpdateStatusRequest(_) => handle_update_status_request_msg(installed_types, msg, s),
        APIRequest::GetThenDeleteRequest(_) => handle_get_then_delete_request_msg(msg, s),
        APIRequest::GetThenUpdateRequest(_) => handle_get_then_update_request_msg(installed_types, msg, s),
    }
}

pub open spec fn handle_request(installed_types: InstalledTypes) -> APIServerAction {
    Action {
        precondition: |input: APIServerActionInput, s: APIServerState| {
            &&& input.recv is Some
            &&& input.recv->0.content.is_APIRequest()
        },
        transition: |input: APIServerActionInput, s: APIServerState| {
            let (s_prime, etcd_resp) = transition_by_etcd(installed_types, input.recv->0, s);
            (s_prime, APIServerActionOutput {
                send: Multiset::singleton(etcd_resp)
            })
        },
    }
}

pub open spec fn api_server(installed_types: InstalledTypes) -> APIServerStateMachine {
    StateMachine {
        init: |s: APIServerState| {
            s.resources == Map::<ObjectRef, DynamicObjectView>::empty()
        },
        actions: set![handle_request(installed_types)],
        step_to_action: |step: APIServerStep| {
            match step {
                APIServerStep::HandleRequest => handle_request(installed_types),
            }
        },
        action_input: |step: APIServerStep, input: APIServerActionInput| {
            input
        }
    }
}


// File: kubernetes_cluster/spec/builtin_controllers/garbage_collector.rs
pub open spec fn run_garbage_collector() -> BuiltinControllersAction {
    Action {
        precondition: |input: BuiltinControllersActionInput, s: ()| {
            let resources = input.resources;
            let key = input.key;
            let owner_references = resources[key].metadata.owner_references->0;
            // The garbage collector is chosen by the top level state machine
            &&& input.choice.is_GarbageCollector()
            // The object exists in the cluster state
            &&& resources.contains_key(input.key)
            // and it has at least one owner reference
            &&& resources[key].metadata.owner_references is Some
            &&& resources[key].metadata.owner_references->0.len() > 0
            // The garbage collector decides whether to delete an object by checking its owner references,
            // it deletes the object if for each owner reference...
            &&& forall |i| #![trigger owner_references[i]] 0 <= i < owner_references.len() ==> {
                // the referred owner object does not exist in the cluster state
                ||| !resources.contains_key(owner_reference_to_object_reference(owner_references[i], key.namespace))
                // or it exists but has a different uid
                // (which means the actual owner was deleted and another object with the same name gets created again)
                ||| resources[owner_reference_to_object_reference(owner_references[i], key.namespace)].metadata.uid != Some(owner_references[i].uid)
            }
        },
        transition: |input: BuiltinControllersActionInput, s: ()| {
            // GC set the preconditions to the object's uid in its delete request
            // See https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/controller/garbagecollector/operations.go#L52-L61
            let preconditions = PreconditionsView {
                uid: input.resources[input.key].metadata.uid,
                resource_version: None,
            };
            let delete_req_msg = built_in_controller_req_msg(
                input.rpc_id_allocator.allocate().1, delete_req_msg_content(input.key, Some(preconditions))
            );
            let output = BuiltinControllersActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            ((), output)
        },
    }
}


// File: kubernetes_cluster/spec/builtin_controllers/state_machine.rs
pub open spec fn builtin_controllers() -> BuiltinControllersStateMachine {
    StateMachine {
        init: |s: ()| {
            true
        },
        actions: set![
            run_garbage_collector(),
        ],
        step_to_action: |step: BuiltinControllersStep| {
            match step {
                BuiltinControllersStep::RunGarbageCollector => run_garbage_collector(),
            }
        },
        action_input: |step: BuiltinControllersStep, input: BuiltinControllersActionInput| {
            input
        }
    }
}


// File: kubernetes_cluster/spec/controller/state_machine.rs
pub open spec fn run_scheduled_reconcile(model: ReconcileModel) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            &&& input.scheduled_cr_key is Some
            &&& input.scheduled_cr_key->0.kind == model.kind
            &&& s.scheduled_reconciles.contains_key(input.scheduled_cr_key->0)
            &&& input.recv is None
            &&& !s.ongoing_reconciles.contains_key(input.scheduled_cr_key->0)
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key->0;
            let (new_allocator, reconcile_id) = s.reconcile_id_allocator.allocate();
            let initialized_ongoing_reconcile = OngoingReconcile {
                triggering_cr: s.scheduled_reconciles[cr_key],
                pending_req_msg: None,
                local_state: (model.init)(),
                reconcile_id: reconcile_id
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, initialized_ongoing_reconcile),
                scheduled_reconciles: s.scheduled_reconciles.remove(cr_key),
                reconcile_id_allocator: new_allocator,
                ..s
            };
            let output = ControllerActionOutput {
                send: Multiset::empty(),
                rpc_id_allocator: input.rpc_id_allocator,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn continue_reconcile(model: ReconcileModel, controller_id: int) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key is Some {
                let cr_key = input.scheduled_cr_key->0;

                &&& cr_key.kind == model.kind
                &&& s.ongoing_reconciles.contains_key(cr_key)
                &&& !(model.done)(s.ongoing_reconciles[cr_key].local_state)
                &&& !(model.error)(s.ongoing_reconciles[cr_key].local_state)
                &&& if s.ongoing_reconciles[cr_key].pending_req_msg is Some {
                    &&& input.recv is Some
                    &&& (input.recv->0.content.is_APIResponse() || input.recv->0.content.is_ExternalResponse())
                    &&& resp_msg_matches_req_msg(input.recv->0, s.ongoing_reconciles[cr_key].pending_req_msg->0)
                } else {
                    input.recv is None
                }
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key->0;
            let reconcile_state = s.ongoing_reconciles[cr_key];
            let resp_o = if input.recv is Some {
                if input.recv->0.content.is_APIResponse() {
                    Some(ResponseContent::KubernetesResponse(input.recv->0.content.get_APIResponse_0()))
                } else {
                    Some(ResponseContent::ExternalResponse(input.recv->0.content.get_ExternalResponse_0()))
                }
            } else {
                None
            };
            let (local_state_prime, req_o) = (model.transition)(reconcile_state.triggering_cr, resp_o, reconcile_state.local_state);
            let (pending_req_msg, send, rpc_id_allocator_prime) = if req_o is Some {
                let pending_req_msg = match req_o->0 {
                    RequestContent::KubernetesRequest(req) => {
                        Some(controller_req_msg(controller_id, cr_key, input.rpc_id_allocator.allocate().1, req))
                    },
                    RequestContent::ExternalRequest(req) => {
                        Some(controller_external_req_msg(controller_id, cr_key, input.rpc_id_allocator.allocate().1, req))
                    }
                };
                (pending_req_msg, Multiset::singleton(pending_req_msg->0), input.rpc_id_allocator.allocate().0)
            } else {
                (None, Multiset::empty(), input.rpc_id_allocator)
            };

            let reconcile_state_prime = OngoingReconcile {
                pending_req_msg: pending_req_msg,
                local_state: local_state_prime,
                ..reconcile_state
            };
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.insert(cr_key, reconcile_state_prime),
                ..s
            };
            let output = ControllerActionOutput {
                send: send,
                rpc_id_allocator: rpc_id_allocator_prime,
            };
            (s_prime, output)
        }
    }
}

pub open spec fn end_reconcile(model: ReconcileModel) -> ControllerAction {
    Action {
        precondition: |input: ControllerActionInput, s: ControllerState| {
            if input.scheduled_cr_key is Some {
                let cr_key = input.scheduled_cr_key->0;

                &&& cr_key.kind == model.kind
                &&& s.ongoing_reconciles.contains_key(cr_key)
                &&& (model.done)(s.ongoing_reconciles[cr_key].local_state) || (model.error)(s.ongoing_reconciles[cr_key].local_state)
                &&& input.recv is None
            } else {
                false
            }
        },
        transition: |input: ControllerActionInput, s: ControllerState| {
            let cr_key = input.scheduled_cr_key->0;
            let s_prime = ControllerState {
                ongoing_reconciles: s.ongoing_reconciles.remove(cr_key),
                ..s
            };
            let output = ControllerActionOutput {
                send: Multiset::empty(),
                rpc_id_allocator: input.rpc_id_allocator,
            };
            (s_prime, output)
        }
    }
}

pub open spec fn controller(model: ReconcileModel, controller_id: int) -> ControllerStateMachine {
    StateMachine {
        init: |s: ControllerState| {
            s == ControllerState {
                scheduled_reconciles: Map::<ObjectRef, DynamicObjectView>::empty(),
                ongoing_reconciles: Map::<ObjectRef, OngoingReconcile>::empty(),
                reconcile_id_allocator: ReconcileIdAllocator {
                    reconcile_id_counter: 0,
                },
            }
        },
        actions: set![
            run_scheduled_reconcile(model),
            continue_reconcile(model, controller_id),
            end_reconcile(model)
        ],
        step_to_action: |step: ControllerStep| {
            match step {
                ControllerStep::RunScheduledReconcile => run_scheduled_reconcile(model),
                ControllerStep::ContinueReconcile => continue_reconcile(model, controller_id),
                ControllerStep::EndReconcile => end_reconcile(model),
            }
        },
        action_input: |step: ControllerStep, input: ControllerActionInput| {
            input
        }
    }
}


// File: kubernetes_cluster/spec/external/state_machine.rs
pub open spec fn transition_by_external(model: ExternalModel, req_msg: Message, resources: StoredState, s: ExternalState) -> (ExternalState, Message)
    recommends
        req_msg.content.is_ExternalRequest(),
{
    let (inner_s_prime, resp) = (model.transition)(req_msg.content.get_ExternalRequest_0(), s.state, resources);
    let s_prime = ExternalState {
        state: inner_s_prime,
        ..s
    };
    let resp_msg = form_external_resp_msg(req_msg, resp);
    (s_prime, resp_msg)
}

pub open spec fn handle_external_request(model: ExternalModel) -> ExternalAction {
    Action {
        precondition: |input: ExternalActionInput, s: ExternalState| {
            &&& input.recv is Some
            &&& input.recv->0.content.is_ExternalRequest()
        },
        transition: |input: ExternalActionInput, s: ExternalState| {
            let req_msg = input.recv->0;
            let resources = input.resources;
            let (s_prime, resp_msg) = transition_by_external(model, req_msg, resources, s);
            (s_prime, ExternalActionOutput {
                send: Multiset::singleton(resp_msg),
            })
        },
    }
}

pub open spec fn external(model: ExternalModel) -> ExternalStateMachine {
    StateMachine {
        init: |s: ExternalState| {
            s.state == (model.init)()
        },
        actions: set![handle_external_request(model)],
        step_to_action: |step: ExternalStep| {
            match step {
                ExternalStep::HandleExternalRequest => handle_external_request(model),
            }
        },
        action_input: |step: ExternalStep, input: ExternalActionInput| {
            input
        }
    }
}


// File: kubernetes_cluster/spec/network/state_machine.rs
pub open spec fn deliver() -> Action<NetworkState, MessageOps, ()> {
    Action {
        precondition: |msg_ops: MessageOps, s: NetworkState| {
            msg_ops.recv is Some ==> s.in_flight.contains(msg_ops.recv->0)
        },
        transition: |msg_ops: MessageOps, s: NetworkState| {
            if msg_ops.recv is Some {
                let s_prime = NetworkState {
                    in_flight: s.in_flight.remove(msg_ops.recv->0).add(msg_ops.send)
                };
                (s_prime, ())
            } else {
                let s_prime = NetworkState {
                    in_flight: s.in_flight.add(msg_ops.send)
                };
                (s_prime, ())
            }
        },
    }
}

pub open spec fn network() -> NetworkStateMachine<NetworkState, MessageOps> {
    NetworkStateMachine {
        init: |s: NetworkState| s.in_flight == Multiset::<Message>::empty(),
        deliver: deliver(),
    }
}


// File: kubernetes_cluster/spec/pod_monkey/state_machine.rs
pub open spec fn create_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let create_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                create_req_msg_content(
                    input.pod.metadata.namespace->0,
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(create_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn delete_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let delete_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                // Monkey does not need a precondition to constrain itself.
                delete_req_msg_content(input.pod.object_ref(), None)
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(delete_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn update_pod() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let update_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                update_req_msg_content(
                    input.pod.metadata.namespace->0,
                    input.pod.metadata.name->0,
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(update_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn update_pod_status() -> PodMonkeyAction {
    Action {
        precondition: |input: PodMonkeyActionInput, s: ()| {
            true
        },
        transition: |input: PodMonkeyActionInput, s: ()| {
            let update_status_req_msg = pod_monkey_req_msg(
                input.rpc_id_allocator.allocate().1,
                update_status_req_msg_content(
                    input.pod.metadata.namespace->0,
                    input.pod.metadata.name->0,
                    input.pod.marshal()
                )
            );

            let s_prime = s;
            let output = PodMonkeyActionOutput {
                send: Multiset::singleton(update_status_req_msg),
                rpc_id_allocator: input.rpc_id_allocator.allocate().0,
            };
            (s_prime, output)
        },
    }
}

pub open spec fn pod_monkey() -> PodMonkeyStateMachine {
    StateMachine {
        init: |s: ()| {
            true
        },
        actions: set![create_pod(), delete_pod(), update_pod(), update_pod_status()],
        step_to_action: |step: PodMonkeyStep| {
            match step {
                PodMonkeyStep::CreatePod => create_pod(),
                PodMonkeyStep::UpdatePod => update_pod(),
                PodMonkeyStep::UpdatePodStatus => update_pod_status(),
                PodMonkeyStep::DeletePod => delete_pod(),
            }
        },
        action_input: |step: PodMonkeyStep, input: PodMonkeyActionInput| {
            input
        }
    }
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


// File: kubernetes_cluster/proof/controller_runtime_liveness.rs
impl Cluster {

pub open spec fn pending_req_msg_is(controller_id: int, s: ClusterState, key: ObjectRef, req: Message) -> bool {
    s.ongoing_reconciles(controller_id)[key].pending_req_msg == Some(req)
}

}



// File: kubernetes_cluster/proof/controller_runtime_safety.rs
impl Cluster {

pub open spec fn every_msg_from_key_is_pending_req_msg_of(
    controller_id: int, key: ObjectRef
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            &&& msg.src == HostId::Controller(controller_id, key)
            &&& msg.content.is_APIRequest()
            &&& msg.dst.is_APIServer()
            &&& s.in_flight().contains(msg)
        } ==> {
            &&& s.ongoing_reconciles(controller_id).contains_key(key)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
        }
    }
}

}



// File: kubernetes_cluster/proof/network.rs
impl Cluster {

pub open spec fn every_in_flight_req_msg_from_controller_has_valid_controller_id(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && msg.content.is_APIRequest()
            && msg.src.is_Controller()
            ==> self.controller_models.contains_key(msg.src.get_Controller_0())
    }
}

}



// File: kubernetes_cluster/proof/objects_in_store.rs
impl Cluster {

pub open spec fn etcd_object_is_weakly_well_formed(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& obj.metadata.well_formed_for_namespaced()
        &&& obj.object_ref() == key
        &&& obj.metadata.resource_version->0 < s.api_server.resource_version_counter
        &&& obj.metadata.uid->0 < s.api_server.uid_counter
    }
}

pub open spec fn each_object_in_etcd_is_weakly_well_formed() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> Self::etcd_object_is_weakly_well_formed(key)(s)
    }
}

pub open spec fn etcd_object_is_well_formed(self, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& Self::etcd_object_is_weakly_well_formed(key)(s)
        &&& unmarshallable_object(obj, self.installed_types)
        &&& valid_object(obj, self.installed_types)
    }
}

pub open spec fn each_builtin_object_in_etcd_is_well_formed(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && !key.kind.is_CustomResourceKind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub open spec fn each_custom_object_in_etcd_is_well_formed<T: CustomResourceView>(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && key.kind == T::kind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub open spec fn etcd_is_finite() -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().dom().finite()
}

}



// File: kubernetes_cluster/spec/install_helpers.rs
impl Cluster {

pub open spec fn installed_type<T: CustomResourceView>() -> InstalledType {
    InstalledType {
        unmarshallable_spec: |v: Value| T::unmarshal_spec(v) is Ok,
        unmarshallable_status: |v: Value| T::unmarshal_status(v) is Ok,
        valid_object: |obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.state_validation(),
        valid_transition: |obj, old_obj: DynamicObjectView| T::unmarshal(obj)->Ok_0.transition_validation(T::unmarshal(old_obj)->Ok_0),
        marshalled_default_status: || T::marshal_status(T::default().status()),
    }
}

pub open spec fn type_is_installed_in_cluster<T: CustomResourceView>(self) -> bool {
    let string = T::kind().get_CustomResourceKind_0();
    &&& self.installed_types.contains_key(string)
    &&& self.installed_types[string] == Self::installed_type::<T>()
}

}



// File: controllers/vreplicaset_controller/model/install.rs
impl Marshallable for VReplicaSetReconcileState {

    uninterp spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

}



// File: controllers/vreplicaset_controller/proof/helper_lemmas.rs
	#[verifier::external_body]
pub proof fn matching_pods_equal_to_matching_pod_entries_values(vrs: VReplicaSetView, s: StoredState)
    ensures
        matching_pods(vrs, s) =~= matching_pod_entries(vrs, s).values()
	{
		unimplemented!()
	}


// File: controllers/vreplicaset_controller/proof/predicate.rs
pub open spec fn matching_pod_entries(vrs: VReplicaSetView, resources: StoredState) -> Map<ObjectRef, DynamicObjectView> {
    Map::new(
        |key: ObjectRef| {
            let obj = resources[key];
            &&& resources.contains_key(key)
            &&& owned_selector_match_is(vrs, obj)
        },
        |key: ObjectRef| {
           resources[key]
        },
    )
}

pub open spec fn req_msg_is_get_then_delete_matching_pod_req(
    vrs: VReplicaSetView, controller_id: int, req_msg: Message,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let request = req_msg.content.get_APIRequest_0();
        let key = request.get_GetThenDeleteRequest_0().key;
        let obj = s.resources()[key];
        let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
        let filtered_pods = state.filtered_pods.unwrap();
        let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
        let diff = state.reconcile_step.get_AfterDeletePod_0();
        // Basic requirements.
        &&& req_msg.dst == HostId::APIServer
        &&& req_msg.content.is_APIRequest()
        &&& request.is_GetThenDeleteRequest()
        // We require the key we are deleting is a pod in etcd owned by vrs.
        &&& s.resources().contains_key(key)
        &&& matching_pods(vrs, s.resources()).contains(obj)
        // We further require that the attached owner reference is the vrs 
        // controller owner reference.
        &&& request.get_GetThenDeleteRequest_0().owner_ref
            == vrs.controller_owner_ref()
        // We further require that the key of the sent request is the last index of
        // filtered_pods.
        &&& key == filtered_pod_keys[diff as int]
    }
}


// File: controllers/vreplicaset_controller/trusted/liveness_theorem.rs
pub open spec fn matching_pods(vrs: VReplicaSetView, resources: StoredState) -> Set<DynamicObjectView> {
    resources.values().filter(|obj: DynamicObjectView| owned_selector_match_is(vrs, obj))
}

pub open spec fn owned_selector_match_is(vrs: VReplicaSetView, obj: DynamicObjectView) -> bool {
    &&& obj.kind == PodView::kind()
    &&& obj.metadata.namespace is Some
    &&& obj.metadata.namespace == vrs.metadata.namespace
    &&& obj.metadata.owner_references_contains(vrs.controller_owner_ref())
    &&& vrs.spec.selector.matches(obj.metadata.labels.unwrap_or(Map::empty()))
    &&& obj.metadata.deletion_timestamp is None
}


pub trait CustomResourceView : ResourceView {}

// File: controllers/vreplicaset_controller/proof/liveness/api_actions.rs
pub proof fn lemma_get_then_delete_matching_pod_request_deletes_matching_pod_and_returns_ok(
    s: ClusterState, s_prime: ClusterState, vrs: VReplicaSetView, cluster: Cluster, controller_id: int, 
    msg: Message,
) -> (resp_msg: Message)
    requires
        cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
        req_msg_is_get_then_delete_matching_pod_req(vrs, controller_id, msg)(s),
        Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
        cluster.each_builtin_object_in_etcd_is_well_formed()(s),
        cluster.each_custom_object_in_etcd_is_well_formed::<VReplicaSetView>()(s),
        cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s),
        Cluster::every_msg_from_key_is_pending_req_msg_of(controller_id, vrs.object_ref())(s),
        no_other_pending_request_interferes_with_vrs_reconcile(vrs, controller_id)(s),
        Cluster::etcd_is_finite()(s),
        cluster.type_is_installed_in_cluster::<VReplicaSetView>(),
    ensures
        resp_msg == handle_get_then_delete_request_msg(msg, s.api_server).1,
        resp_msg.content.get_get_then_delete_response().res is Ok,
        // identifies specific pod deleted.
        ({
            let state = VReplicaSetReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[vrs.object_ref()].local_state).unwrap();
            let filtered_pods = state.filtered_pods.unwrap();
            let filtered_pod_keys = filtered_pods.map_values(|p: PodView| p.object_ref());
            let diff = state.reconcile_step.get_AfterDeletePod_0();
            matching_pods(vrs, s_prime.resources()) == matching_pods(vrs, s.resources()).remove(
                s.resources()[filtered_pod_keys[diff as int]]
            )
        }),
        // should be an obvious corollary of `generated_name_is_unique`.
        matching_pods(vrs, s.resources()).len() == matching_pods(vrs, s_prime.resources()).len() + 1,
{
    let r = arbitrary(); // TODO -- replace with the right return value/expression, and finish 
                         // the proof
    r
}



}
