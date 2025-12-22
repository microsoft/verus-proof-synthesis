use vstd::prelude::*;
use vstd::assert_seqs_equal;
use deps_hack::k8s_openapi;

fn main() {}

verus!{

pub type ResourceVersion = int;
pub type VReplicaSetStatusView = EmptyStatusView;
pub type StringView = Seq<char>;
pub type Uid = int;
pub type EmptyStatusView = ();

// File: vstd_ext/string_map.rs
#[verifier(external_body)]
pub struct StringMap {
    inner: std::collections::BTreeMap<std::string::String, std::string::String>,
}

impl View for StringMap {
    type V = Map<Seq<char>, Seq<char>>;

    uninterp spec fn view(&self) -> Map<Seq<char>, Seq<char>>;
}

impl DeepView for StringMap {
    type V = Map<Seq<char>, Seq<char>>;

    open spec fn deep_view(&self) -> Map<Seq<char>, Seq<char>> {
        self@
    }
}

impl StringMap {
    #[verifier(external_body)]
    pub fn new() -> (m: Self)
        ensures m@ == Map::<Seq<char>, Seq<char>>::empty(),
    {
        unimplemented!()
    }
}


// File: kubernetes_api_objects/exec/resource.rs
macro_rules! implement_field_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        verus! {

        #[verifier(external_body)]
        pub struct $t {
            inner: $it,
        }

        }

        implement_view_trait!($t, $vt);
        implement_deep_view_trait!($t, $vt);
    };
}


macro_rules! implement_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl View for $t {
            type V = $vt;

            uninterp spec fn view(&self) -> $vt;
        }

        }
    };
}



macro_rules! implement_deep_view_trait {
    ($t:ty, $vt:ty) => {
        verus! {

        impl DeepView for $t {
            type V = $vt;

            open spec fn deep_view(&self) -> $vt {
                self@
            }

}}}}

macro_rules! implement_object_wrapper_type {
    ($t:ident, $it:ty, $vt:ty) => {
        implement_field_wrapper_type!($t, $it, $vt);

        verus! {

        impl $t {

            #[verifier(external_body)]
            pub fn metadata(&self) -> (metadata: ObjectMeta)
                ensures metadata@ == self@.metadata,
	{
		unimplemented!()
	}

}}}}



// File: kubernetes_api_objects/spec/affinity.rs
pub struct AffinityView {}


// File: kubernetes_api_objects/spec/common.rs
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


// File: kubernetes_api_objects/spec/label_selector.rs
pub struct LabelSelectorView {
    pub match_labels: Option<Map<StringView, StringView>>,
}

impl LabelSelectorView {

    pub open spec fn matches(self, labels: Map<StringView, StringView>) -> bool {
        if self.match_labels is None {
            true
        } else {
            let match_labels = self.match_labels->0;
            forall |k, v| match_labels.contains_pair(k, v) ==> labels.contains_pair(k, v)
        }
    }

}

// File: kubernetes_api_objects/exec/object_meta.rs
implement_field_wrapper_type!(
    ObjectMeta,
    k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta,
    ObjectMetaView
);



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

    pub open spec fn well_formed_for_namespaced(self) -> bool {
        &&& self.name is Some
        &&& self.namespace is Some
        &&& self.resource_version is Some
        &&& self.uid is Some
    }

}



// File: kubernetes_api_objects/spec/owner_reference.rs
implement_field_wrapper_type!(
    OwnerReference,
    k8s_openapi::apimachinery::pkg::apis::meta::v1::OwnerReference,
    OwnerReferenceView
);


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


// File: controllers/vreplicaset_controller/trusted/spec_types.rs
pub struct VReplicaSetView {
    pub metadata: ObjectMetaView,
    pub spec: VReplicaSetSpecView,
    pub status: Option<VReplicaSetStatusView>,
}

impl VReplicaSetView {

    pub open spec fn well_formed(self) -> bool {
        &&& self.metadata.well_formed_for_namespaced()
        &&& self.state_validation()
    }

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
    pub open spec fn kind() -> Kind { Kind::CustomResourceKind("vreplicaset"@) }

    #[verifier(inline)]
    pub open spec fn state_validation(self) -> bool {
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

}


pub struct VReplicaSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub template: Option<PodTemplateSpecView>,
}


// File: kubernetes_api_objects/spec/resource.rs
pub trait ResourceView: Sized {

    spec fn kind() -> Kind;

    spec fn state_validation(self) -> bool;

}

// File: controllers/vreplicaset_controller/model/reconciler.rs
pub open spec fn make_owner_references_spec(v_replica_set: VReplicaSetView) -> Seq<OwnerReferenceView> 
{ 
    seq![v_replica_set.controller_owner_ref()] 
}

// File: controllers/vreplicaset_controller/trusted/exec_types.rs
implement_object_wrapper_type!(
    VReplicaSet,
    deps_hack::VReplicaSet,
    VReplicaSetView
);

implement_field_wrapper_type!(
    VReplicaSetSpec,
    deps_hack::VReplicaSetSpec,
    VReplicaSetSpecView
);

impl VReplicaSet {

    #[verifier(external_body)]
    pub fn controller_owner_ref(&self) -> (owner_reference: OwnerReference)
        ensures owner_reference@ == self@.controller_owner_ref(),
	{
		unimplemented!()
	}

}

// File: controllers/vreplicaset_controller/exec/reconciler.rs
pub fn make_owner_references(v_replica_set: &VReplicaSet) -> (owner_references: Vec<OwnerReference>)
    requires v_replica_set@.well_formed(),
    ensures owner_references.deep_view() ==  make_owner_references_spec(v_replica_set@),
{
    let mut owner_references = Vec::new();
    owner_references.push(v_replica_set.controller_owner_ref());
    proof {
        assert_seqs_equal!(
            owner_references.deep_view(),
            make_owner_references_spec(v_replica_set@)
        );
    }
    owner_references
}




}
