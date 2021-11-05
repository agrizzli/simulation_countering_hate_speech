extensions [nw]

;; Link type to represent follower connections
directed-link-breed [ followings following ]

;; Model persons in the network as agents
breed [ persons person ]

;; Model posts as agents
breed [ posts post ]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Configuration ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

globals [
  ; List of influening ends (those to whom people follow) of the edges (every node can appear multiple times here)
  influence_list

  ; ID of the next post created
  next_post_id

  ; Smoothed versions of path length of posts
  smoothed_path_length_hater
  smoothed_path_length_normal
  smoothed_path_length_activist

  ; Smoothed versions of posts amounts
  smoothed_num_posts_hater
  smoothed_num_posts_normal
  smoothed_num_posts_activist

  ; Amounts of reposts
  percentage_reposts_hater
  percentage_reposts_normal
  percentage_reposts_activist

]

persons-own [
  ;; User's hate score (or opinion)
  t_hate_score

  ;; Only for export
  t_is_hater?

  ;; Indicates activists with other behavior
  t_is_activist?

  ;; Community ID
  t_community_id

  ;; Reposts done in the current round
  cur_reposts_per_round
  max_reposts_per_round
]

posts-own [
  ;; Post's hate score (or opinion) = Original hatescore of the author at post time
  t_hate_score

  ;; Author ID (who number)
  t_author_id

  ;; The author of the post
  t_author

  ;; List of previous reposters
  t_reposter_ids

  ;; Amount of times it has been reposted
  t_repost_path_length

  ;; Original post ID
  t_original_post_id

  ;; Round when post created (necessary for clean up)
  t_tick

  ;; Indicated for how many ticks the post will be deferred,
  ;; so that it will have no effect in influencing neighbors nor could be reposted
  t_ticks_to_defer

  ;; Amount of ticks, for which the original post was deferred.
  t_ticks_deferred

  ;; Indicates activists' posts
  t_is_activist?
]

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Setup procedures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to setup
  random-seed new-seed

  clear-all
  clear-output
  set-default-shape persons "circle 2"
  set-default-shape posts "circle"

  ; Init globals
  set influence_list []
  set next_post_id 0
  set smoothed_path_length_hater 0
  set smoothed_path_length_normal 0
  set smoothed_path_length_activist 0
  set percentage_reposts_hater 0
  set percentage_reposts_normal 0
  set percentage_reposts_activist 0

  ;; make the initial network of two persons and an edge
  make-node [] 0.4                ;; first node, unattached
  make-node (list person 0) 0.4   ;; second node, attached to first node

  reset-ticks
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main procedures ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to go
  ; Stops if society becomes to hateful.
  ; This is to protect against memory overflow,
  ; since amount of hateful posts might develop exponentially
  if swap-to-hate [ stop ]

  ; Stop if ticks exceeds simulation limits
  if ticks > dynamics_until_ticks and ticks > grow_until_size [ stop ]

  ;; new edge is green, old edges are gray
  if count persons < grow_until_size [ grow-network ]

  if layout? [ layout ]

  ; Propagate opinion spread and apply some counter measures
  if ticks >= dynamics_from_ticks and ticks <= dynamics_until_ticks
  [
    ;; In activists counter mode, pick new activist from existing nodes
    if activists_mode?
    [ convince-to-become-activist ]

    propagate-opinions
  ]

  tick
end

;; Grow network by adding new node and connecting it
;; by preferential attachment and other params, e.g.
to grow-network

  ; Sample hate score (opinion) for the new node
  ; Exclude outliers with > 1.0 hate score and use them as extrem core with hate score 1.0
  let hate-score random-gamma hate_score_dist_alpha hate_score_dist_lambda
  if hate-score > 1.0 [ set hate-score 1.0 ]

  ; Set amount of connection
  let n_conn n_following_conn_normal
  if hate-score >= hate_score_hater [
    set n_conn n_following_conn_hater
  ]

  ; Select node to connect
  let old-nodes []
  let n_conn_created 0
  while [ n_conn_created < n_conn ] [

    let old-node find-partner (hate-score >= hate_score_hater)
    if not member? old-node old-nodes
    [
      set old-nodes (lput old-node old-nodes)
      set n_conn_created (n_conn_created + 1)
    ]
  ]

  ; Create new node and connect it to the found one
  make-node old-nodes hate-score
end

;; This code is the heart of the "preferential attachment" mechanism.
;; We first pick hateful or normal link ends and then one of the following ends,
;; which correspond to the out-degree (influence connection)
to-report find-partner [ for_hater? ]

  ; Normals connects by preferential attachment independent of hater or not
  let partner_list influence_list

  ; Haters connect always only to haters, if there is any
  if for_hater? [
    let hater_list (filter filter-person-is-hater influence_list)
    let non_activist_list (filter filter-person-is-non-activist influence_list)

    ifelse random-float 1.0 <= p_hater_follows_hater and num-hateful-persons >= n_following_conn_hater
    [ set partner_list hater_list ]
    [ set partner_list non_activist_list ] ;; Never follow activists as hater
  ]

  ; Get a random node according to the preferential attachment setting
  report one-of partner_list
end

;; Try to find an additional appropriate partner (followee) for new activist
to-report find-activist-partner [ but_not_person already_partners ]
  ;; Try to pick some partner or else return nobody
  let activist nobody

  ;; 1. First try to connect to already existing activists
  let activists_list (filter [p -> filter-person-could-be-activist-partner but_not_person already_partners p] influence_list)
  ifelse not empty? activists_list
  [ set activist one-of activists_list ]
  [

    ;; 2. If no activist partner found then look for an alternative potential activist
    set activists_list (filter [p -> filter-person-could-be-potential-partner but_not_person already_partners p] influence_list)
    ifelse not empty? activists_list
    [ set activist one-of activists_list ]
    [

      ;; 3. Finally look for someone from non-haters
      set activists_list (filter [p -> filter-person-could-be-normal-partner but_not_person already_partners p] influence_list)
      if not empty? activists_list
      [ set activist one-of activists_list ]
    ]
  ]

  report activist
end

;; Used for creating a new initial node with given configuration
to make-node [old-nodes hate-score]
  create-persons 1
  [
    ;; Set provided hate score
    set t_hate_score hate-score

    ;; By default there are no activists during the phase of network growth
    set t_is_activist? false

    ; Set color
    set color blue
    set size 1.5

    let follower_is_hater? false
    if person-is-hater [
      set color red
      set follower_is_hater? true
    ]

    ; Connect new node to given nodes
    ifelse length old-nodes > 0
    [
      foreach old-nodes [ old-node ->

        create-influence-connection old-node self
        ;; position the new node near its partner
        move-to old-node
        fd 16

        ; Decide whether to follow back the new node
        let follows_back false
        ; In special case of the first pair of two node, do follow always
        ; Else act according to the probability for hateful/normal nodes
        ifelse who = 1
        [ set follows_back true ]
        [
          ; Set threshold
          let p_back_follows 0.0

          ; In case of hater to hater, follow back according to the probability
          if follower_is_hater? and filter-person-is-hater old-node
          [ set p_back_follows p_hater_back_follows_hater ]

          ; In case of hater to normal, follow back according to the probability
          if follower_is_hater? and filter-person-is-normal old-node
          [ set p_back_follows p_hater_back_follows_normal ]

          ; In case of normal to normal, follow back according to the probability
          if not follower_is_hater? and filter-person-is-normal old-node
          [ set p_back_follows p_normal_back_follows_normal ]

          ; In case of normal to hater,  follow back according to the probability
          if not follower_is_hater? and filter-person-is-hater old-node
          [ set p_back_follows p_hater_back_follows_normal ]

          if random-float 1.0 <= p_back_follows
          [ set follows_back true ]
        ]

        ; Do back-follow
        if follows_back [
          create-back-influence-connection self old-node
        ]
      ]
    ]
    ; This is just for the very first node
    ; Add new node to the influencer list, because it is the only existing
    [ set influence_list (lput self influence_list) ]
  ]
end

;; Create a following connection
;; Target node will get more weight as influencer
to create-influence-connection [ followee follower ]
  ; Influence goes from followee (influence) to follower
  ask followee [
    create-following-to follower [ set color green ]
  ]

  ; Add node (to whom one follows) to list of influencing nodes,
  ; because this is one to whom the new node is following
  set influence_list (lput followee influence_list)
  set influence_list (lput followee influence_list)
  set influence_list (lput follower influence_list)
end


;; Create a back-following connection
;; Target node will get more weight as influencer
to create-back-influence-connection [ followee follower ]
  ; Influence goes from followee (influence) to follower
  ask followee [
    create-following-to follower [ set color green ]
  ]

  ; Add node (to whom one follows) to list of influencing nodes,
  ; because this is one to whom the new node is following
  set influence_list (lput followee influence_list)
end



;; Propagate opinions according to a confidence bounded model.
;; We use Deffuant-Weisbuch diffusion model, however only in one direction.
;; This way a post can influence all the followers of the author once, if posts' opinion (hate score) is in bounds.
;; There is now back-inflluence of the author by the followers. Influence on the author can only be achieved,
;; when people whom he/she is following create a post.
;;
;; In every round select nodes which are going to publish content according to probabilities.
;; Publish a post with the original hate score of the node
to propagate-opinions
  ; Propagate the opinion of the posts from last round
  if diffuse? [ diffuse-opinions ]

  hide-connections-without-influence

  ; Repost posts
  if repost? [ repost-posts ]

  ; Clean up old posts
  cleanup-old-posts

  ; Create new posts for the current round/tick
  create-new-posts
end

;; Influence receivers of the posts which are not deferred
to diffuse-opinions
  ask posts with [ t_ticks_to_defer < 1 ] [
    let post_hate_score t_hate_score

    let followee (person t_author_id)
    ask followee [
      let followers out-following-neighbors
      ask followers [

        ;; Adapt hate score, if difference is in accepted bounds
        let opinion_diff (post_hate_score - t_hate_score)
        let accepted_diff opinon-acceptance-mapping t_hate_score

        ;; Do not adapt opinion of stubborn activists
        if activists_mode? and stubborn_activists? and person-is-activist
        [ set accepted_diff 0 ]

        ;; If opinion difference is small enough than difuse
        if abs opinion_diff <= accepted_diff
        [ set t_hate_score (t_hate_score + mixing_parameter * (opinion_diff)) ]

        ; Adapt colors
        ifelse person-is-normal
        [ set color blue ]
        [ set color red ]

        ; Adapt colors and properties in case of activists
        if activists_mode? and person-is-activist
        [
          ; Adapt activist property if hate score moved upwards
          ifelse t_hate_score >= hate_score_potential_activist
          [ set t_is_activist? false ]
          [ set color white ]
        ]
      ]
    ]
  ]
end

;; Hide follower connections, which have no influence on opinion change
to hide-connections-without-influence []
  ask persons [
    let followee self
    let followers out-following-neighbors
    let follower_hate_score t_hate_score
    ask followers [
      let opinion_diff (follower_hate_score - t_hate_score)
      let accepted_diff opinon-acceptance-mapping t_hate_score

      ;; Hide connection if opinion difference too high
      if abs opinion_diff > accepted_diff and display_only_influence? [
        let following-connection in-following-from followee
        ask following-connection [ set hidden? true ]
      ]
    ]
  ]
end

;; Repost posts with given probabilities
to repost-posts []
  ;; Setup some posting limits according to settings
  setup-repost-limits

  ;; Get the followers of the original poster and perhaps repost
  let reposts []
  let num_reposts_hater 0
  let num_reposts_normal 0
  let num_reposts_activist 0

  ask posts with [ t_ticks_to_defer < 1 ] [
    ; Hater's post?
    let post_hater false
    if post-is-hater [ set post_hater true ]

    ; Activist post?
    let post_activist false
    if post-is-activist [ set post_activist true ]

    ; Store vars for later post cloning
    let original_post self
    let post_reposter_ids t_reposter_ids

    ; Decrease probability when reposting deferred
    let p_repost_deferred_post_seq 1
    if t_ticks_deferred > 0 [
      repeat t_ticks_deferred [
        set p_repost_deferred_post_seq (p_repost_deferred_post_seq * p_repost_deferred_post)
      ]
    ]

    ask person t_author_id [
      let followers out-following-neighbors
      ask followers [
        ; Hater?
        let node_hater false
        if person-is-hater [ set node_hater true ]

        ; Activist
        let node_activist false
        if person-is-activist [ set node_activist true ]

        ; Select reposting probability
        let p_repost p_normal_reposts_normal
        if node_hater and post_hater [ set p_repost p_hater_reposts_hater ]
        if node_hater and not post_hater [ set p_repost p_hater_reposts_normal ]
        if not node_hater and post_hater [ set p_repost p_normal_reposts_hater ]

        ;; In activists' mode apply additional parameters
        if activists_mode?
        [
          if node_activist and post_activist [ set p_repost p_activist_reposts_activist ]
          if node_hater and post_activist [ set p_repost 0 ]
          if node_activist and post_hater [ set p_repost 0 ]
          if not node_hater and not node_activist and post_activist [ set p_repost p_normal_reposts_activist ]
        ]

        ; Consider reposting probability for deferred posts
        set p_repost (p_repost * p_repost_deferred_post_seq)

        ; Do repost? if probability in range
        ; and if not already reposted this post
        if p_repost > 0 and (random-float 1.0) <= p_repost and not member? who post_reposter_ids and cur_reposts_per_round < max_reposts_per_round [

          set cur_reposts_per_round cur_reposts_per_round + 1

          ; Just add a tuple to the list
          set reposts (lput (list self original_post) reposts)

          ; Count reposts by haters / normals
          ifelse node_hater
          [ set num_reposts_hater (num_reposts_hater + 1) ]
          [ set num_reposts_normal (num_reposts_normal + 1) ]

          if activists_mode? and node_activist
          [ set num_reposts_activist (num_reposts_activist + 1) ]
        ]
      ]
    ]
  ]

  ;; Update smoothed metrics for number of reposts
  update-smoothed-num-reposts num_reposts_normal num_reposts_hater num_reposts_activist

  ;; Finally create repostings as batch procedure
  create-reposts-as-batch reposts
end

;; Reinitialise limits for amounts of posts per round
to setup-repost-limits

  ;; Reset amount of reposts by each person
  ask list-hateful-persons [
    set cur_reposts_per_round 0
    set max_reposts_per_round max_reposts_by_haters
  ]
  ask list-normal-persons [
    set cur_reposts_per_round 0
    set max_reposts_per_round max_reposts_by_normals
  ]

  ;; In activists' mode use additional limitations
  if activists_mode?
  [
    ask list-activist-persons [
      set cur_reposts_per_round 0
      set max_reposts_per_round max_reposts_by_activists
    ]
  ]
end

to update-smoothed-num-reposts [num_reposts_normal num_reposts_hater num_reposts_activist]

  ; Set global percentage of reposts by hater / normal
  ; It is amount of conducted reposts by hater/ normal normalised by number of persons in corresponding group
  let smoothness 0.99
  if num-hateful-persons > 0
  [ set percentage_reposts_hater smoothness * percentage_reposts_hater + (1 - smoothness) * (num_reposts_hater / num-hateful-persons * 100) ]
  if num-normal-persons > 0
  [ set percentage_reposts_normal smoothness * percentage_reposts_normal + (1 - smoothness) * (num_reposts_normal / num-normal-persons * 100) ]

  if activists_mode? and num-activist-persons > 0
  [ set percentage_reposts_activist smoothness * percentage_reposts_activist + (1 - smoothness) * (num_reposts_activist / num-activist-persons * 100) ]
end


to create-reposts-as-batch [ reposts ]

  ;; Create reposts as batch
  foreach reposts [ r ->
    ; Get poster and reposter
    let reposter first r
    let original_post last r

    ; Get parameters from author
    let post_hate_score 0
    let reposter_id 0
    ask reposter [
      set post_hate_score t_hate_score
      set reposter_id who
    ]

    ; Get post vars
    let post_color blue
    let post_repost_path_length 0
    let post_original_post_id 0
    let post_reposter_ids []
    let post_author_id 0
    let post_ticks_to_defer 0
    let post_is_activist? false
    ask original_post [
      if person-is-hater [ set post_color red ]
      if person-is-activist [ set post_color white ]

      set post_hate_score t_hate_score
      set post_repost_path_length t_repost_path_length
      set post_original_post_id t_original_post_id
      set post_reposter_ids t_reposter_ids
      set post_author_id t_author_id
      set post_is_activist? t_is_activist?

      ; Test deferring probability and then set amount of rounds to defer
      if post-is-hater and (random-float 1.0) <= p_defer_hateful_post
      [ set post_ticks_to_defer 1 ]
    ]

    create-posts 1 [
      ; Set initial params from author
      set t_hate_score post_hate_score
      set t_author reposter
      set t_author_id reposter_id
      set t_reposter_ids (lput post_author_id post_reposter_ids)
      set t_repost_path_length (post_repost_path_length + 1)
      set t_original_post_id post_original_post_id
      set t_tick ticks
      set t_ticks_to_defer post_ticks_to_defer
      set t_ticks_deferred 0
      set t_is_activist? post_is_activist?

      ; Move position at the authors node
      move-to reposter
      set color post_color
    ]
  ]
end

;; Just remove all posts from old round as long as those had not been deferred
to cleanup-old-posts []

  ask posts with [ t_tick + t_ticks_to_defer < ticks ] [ die ]

  ; For deferred posts discount rounds
  ask posts with [ t_tick + t_ticks_to_defer > ticks ] [
    set t_ticks_to_defer (t_ticks_to_defer - 1)
    set t_ticks_deferred (t_ticks_deferred + 1)
  ]
end

;; Create new posts for the current round
to create-new-posts []

  ; Create posts with the probability of publishing
  foreach sort persons [ p ->

    let do_post false
    let post_color blue
    let author_is_activist? false
    ask p [
      ; Determine publishing probability
      let p_publish_post p_publish_post_normal
      if person-is-hater
      [
        set p_publish_post p_publish_post_hater
        set post_color red
      ]

      ;; In activists' mode use activist probabilities
      if activists_mode? and person-is-activist
      [
        set p_publish_post p_publish_post_activist
        set post_color white
        set author_is_activist? true
      ]

      ; Test probability and then add the person as poster
      if (random-float 1.0) <= p_publish_post
      [ set do_post true ]
    ]


    ;; Finally create a post by the person
    if do_post [
      ; Get parameters from author and determine and amounts of rounds to defer
      let post_hate_score 0
      let author_id 0
      let n_ticks_to_defer 0
      ask p [
        set post_hate_score t_hate_score
        set author_id who

        ; Test deferring probability and then set amount of rounds to defer
        if person-is-hater and (random-float 1.0) <= p_defer_hateful_post
        [ set n_ticks_to_defer 1 ]
      ]

      ; Create post
      create-posts 1 [
        ; Set initial params from author
        set t_hate_score post_hate_score
        set t_author p
        set t_author_id author_id
        set t_reposter_ids []
        set t_repost_path_length 0
        set t_original_post_id next_post_id
        set t_tick ticks
        set t_ticks_to_defer n_ticks_to_defer
        set t_ticks_deferred 0
        set t_is_activist? author_is_activist?

        ; Move position at the authors node
        move-to p
        set color post_color
      ]

      ; Increment global next post ID
      set next_post_id (next_post_id + 1)
    ]
  ]
end


;; As countermeasure against haters, pick activists with lower hate score
;; to act with higher activity against haters
to convince-to-become-activist
  let pick_activist? false

  ;; Pick a new activist with some probability
  if random-float 1.0  <= p_convincing_to_become_activist
  [ set pick_activist? true ]

  ;; If there is no activist yet, then create one in the first round
  if num-activist-persons < 1
  [ set pick_activist? true ]

  ;; Early return: Do not pick a new activist
  if not pick_activist?
  [ stop ]
  let activist pick-activist

  ;; Change properties of new activist, which is an indicator for different activity later
  let old-nodes []
  ask activist [
    set t_is_activist? true
    set color white

    ;; In case that person was picked from normals, adapt its hate score
    if not person-is-potential-activist and person-is-normal
    [ set t_hate_score hate_score_potential_activist / 2 ]

    ;; Finally create new additional connections to other activists
    ;; In the case of first activist create connections to normals
    repeat n_following_conn_activist_additional [
      let old-node find-activist-partner self old-nodes

      ;; Skip nobodies. This can happen in some cases at the beginning
      if old-node != nobody
      [ set old-nodes (lput old-node old-nodes) ]
    ]
  ]

  ;; Create new connections
  foreach old-nodes [ old-node ->

    ;; Create new influence connection
    create-activist-influence-connection old-node activist

    ;; Check whether partner node is already back-following
    let is_already_follower false
    ask old-node [
      if member? self in-following-neighbors
      [ set is_already_follower true ]
    ]

    ; Do back-follow
    if random-float 1.0 <= p_activist_back_follows_activist and not is_already_follower
    [ create-activist-influence-connection activist old-node ]
  ]
end

to-report pick-activist
  ;; Pick a new activist from potential group of persons with low hate score
  ;; In the inprobable case that there are no such persons, than pick any non-hateful person
  ;; Pick with uniform probability or by preferential attachment
  let potential_activists []

  ifelse select_activist_by_influence?
  [
    set potential_activists (filter filter-person-is-potential-activist influence_list)

    ;; In case there were no activist with low hate score, then pick some normal person and adapt its hate score
    if empty? potential_activists
    [ set potential_activists (filter filter-person-is-unusual-potential-activist influence_list) ]
  ]
  [
    set potential_activists persons with [ person-is-potential-activist ]

    ;; In case there were no activist with low hate score, then pick some normal person and adapt its hate score
    if not any? potential_activists
    [ set potential_activists persons with [ person-is-unusual-potential-activist ] ]
  ]

  report one-of potential_activists
end

;; Create a following connection
;; Target node will get more weight as influencer
to create-activist-influence-connection [ followee follower ]

  ; Influence goes from followee (influence) to follower
  ask followee [
    create-following-to follower [ set color green ]
  ]

  ; Add node (to whom one follows) to list of influencing nodes,
  ; because this is one to whom the new node is following
  set influence_list (lput followee influence_list)
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Getter/Helper ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Report whether given node is considered hateful
to-report filter-person-is-hater [t]
  let t_is_hater false
  ask t [
    if person-is-hater [
      set t_is_hater true
    ]
  ]
  report t_is_hater
end

;; Report whether given person is considered normal / non-hateful
to-report filter-person-is-normal [t]
  let t_is_normal false
  ask t [
    if person-is-normal [
      set t_is_normal true
    ]
  ]
  report t_is_normal
end

to-report filter-person-is-non-activist [t]
  let t_is_normal false
  ask t [
    if not person-is-activist [
      set t_is_normal true
    ]
  ]
  report t_is_normal
end

;; Filter persons who are potential activists with low hate score but have not become activists yet
to-report filter-person-is-potential-activist [t]
  let t_is_potential_activist false
  ask t [
    if person-is-potential-activist [
      set t_is_potential_activist true
    ]
  ]
  report t_is_potential_activist
end

to-report filter-person-is-unusual-potential-activist [t]
  let t_is_potential_activist false
  ask t [
    if person-is-unusual-potential-activist [
      set t_is_potential_activist true
    ]
  ]
  report t_is_potential_activist
end

;; Filter to find persons who could become new followee of an activist
to-report filter-person-could-be-activist-partner [this_person already_partners potential_partner]
  let is_candidate true

  ask potential_partner [
    ;; Should be an activist
    if not person-is-activist
    [ set is_candidate false ]

    ;; Must not be the same node
    if self = this_person
    [ set is_candidate false ]

    ;; Must not be one of the followers
    if member? this_person in-following-neighbors
    [ set is_candidate false ]

    ;; Must not be one of already connected partners
    if member? self already_partners
    [ set is_candidate false ]
  ]

  report is_candidate
end

;; Alternative to filter-person-could-be-activist-partner if nothing found there
to-report filter-person-could-be-potential-partner [this_person already_partners potential_partner]
  let is_candidate true

  ask potential_partner [
    ;; Should be a potential activist
    if not person-is-potential-activist
    [ set is_candidate false ]

    ;; Must not be the same node
    if self = this_person
    [ set is_candidate false ]

    ;; Must not be one of the followers
    if member? this_person in-following-neighbors
    [ set is_candidate false ]

    ;; Must not be one of already connected partners
    if member? self already_partners
    [ set is_candidate false ]
  ]

  report is_candidate
end

;; Alternative to filter-person-could-be-potential-partner if nothing found there
to-report filter-person-could-be-normal-partner [this_person already_partners potential_partner]
  let is_candidate true

  ask potential_partner [
    ;; Should not be a hater
    if person-is-hater
    [ set is_candidate false ]

    ;; Must not be the same node
    if self = this_person
    [ set is_candidate false ]

    ;; Must not be one of the followers
    if member? this_person in-following-neighbors
    [ set is_candidate false ]

    ;; Must not be one of already connected partners
    if member? self already_partners
    [ set is_candidate false ]
  ]

  report is_candidate
end

;; Reports whether person itself is hater
to-report person-is-hater
  report t_hate_score >= hate_score_hater
end

;; Reports whether person itself is normal
to-report person-is-normal
  report t_hate_score < hate_score_hater
end

;; Report whether person might become activist but is not yet
to-report person-is-potential-activist
  report t_hate_score < hate_score_potential_activist and not t_is_activist?
end

;; Report whether person could exceptionally become activist, although not with usual hate score
to-report person-is-unusual-potential-activist
  report t_hate_score >= hate_score_potential_activist and not person-is-hater and not t_is_activist?
end

to-report person-is-activist
  report t_is_activist?
end

;; Reports whether post itself reflects hater opinion
to-report post-is-hater
  report person-is-hater
end

;; Reports whether post itself reflects normal opinion
to-report post-is-normal
  report person-is-normal
end

to-report post-is-activist
  report person-is-activist
end

to detect-communities
  nw:set-context persons links
  foreach nw:louvain-communities [ [comm] ->
    ask comm [ set t_community_id comm ]
  ]
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Reporter ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Report mean hate score normalized by the amount of nodes
to-report mean-hate-score
  let hate-sum 0
  foreach sort persons [ t ->
    ask t [ set hate-sum (hate-sum + t_hate_score) ]
  ]

  report hate-sum / count persons
end

;; Report mean amount of followers/followees per hateful/normal node
to-report mean-following [ follower? for_haters? ]
  let nodes []
  ifelse for_haters?
  [ set nodes list-hateful-persons ]
  [ set nodes list-normal-persons ]

  let s 0
  ifelse follower?
  [ set s sum [count out-following-neighbors] of nodes ]
  [ set s sum [count in-following-neighbors] of nodes ]
  let c count nodes
  if c > 0 [ report s / c ]
  report 0
end


;; Report mean amount of followers/followees per activist node
to-report mean-following-activist [ follower? ]
  let nodes list-activist-persons

  let s 0
  ifelse follower?
  [ set s sum [count out-following-neighbors] of nodes ]
  [ set s sum [count in-following-neighbors] of nodes ]
  let c count nodes
  if c > 0 [ report s / c ]
  report 0
end

;; Report mean ratio of follower by followee
to-report mean-follower-followee [ for_haters? ]
  let nodes []
  ifelse for_haters?
  [ set nodes list-hateful-persons ]
  [ set nodes list-normal-persons ]

  let s sum [follower-followee] of nodes
  let c count nodes
  if c > 0 [ report s / c ]
  report 0
end


;; Report mean ratio of follower by followee
to-report mean-follower-followee-activist
  let nodes list-activist-persons

  let s sum [follower-followee] of nodes
  let c count nodes
  if c > 0 [ report s / c ]
  report 0
end

;; Report nodes ratio of follower/followee
to-report follower-followee
  let follower count out-following-neighbors
  let followee count in-following-neighbors

  if followee > 0 [ report follower / followee ]

  ;; This should never happen, since every node creates at least one followee connection on joining the network and cannot lose it
  report 0
end

;; Report mean follow probabilities between different node types
to-report mean-follow-prob [ follower_hater? followee_hater? ]
  let nodes []
  ifelse follower_hater?
  [ set nodes list-hateful-persons ]
  [ set nodes list-normal-persons ]

  let s sum [follow-prob followee_hater?] of nodes
  let c count nodes
  if c > 0 [ report s / c ]
  report 0
end

;; Report follow probabilities between different node types for one node
to-report follow-prob [ followee_hater? ]
  ; Get followees
  let followees in-following-neighbors

  ; Get target nodes
  let nodes []
  ifelse followee_hater?
  [ set nodes followees with [ person-is-hater ] ]
  [ set nodes followees with [ person-is-normal ] ]

  let s count nodes
  let c count followees
  if c > 0 [ report s / c ]
  report 0
end

; Report the amount of users with some specific (out/in) degree
to-report percents-persons-with-degree [hater? follower? degree]
  let degrees []
  ifelse hater?
  [ set degrees [count out-following-neighbors] of list-hateful-persons ]
  [ set degrees [count out-following-neighbors] of list-normal-persons ]

  let base []
  ifelse hater?
  [ set base list-hateful-persons ]
  [ set base list-normal-persons ]

  ifelse count base < 1
  [ report 0 ]
  [ report length (filter [ el -> filter-number el degree ] degrees) / count base ]
end

to-report filter-number [el num]
  report el = num
end

; Report amount of links between specific groups
to-report num-connections [ follower_hater? followee_hater? ]
  let num 0

  let nodes []
  ifelse follower_hater?
  [ set nodes list-hateful-persons ]
  [ set nodes list-normal-persons ]

  foreach sort nodes [ n ->
    ask n [
      let followees []
      ifelse followee_hater?
      [ set followees in-following-neighbors with [ person-is-hater ] ]
      [ set followees in-following-neighbors with [ person-is-normal ] ]

      set num (num + count followees)
    ]
  ]

  report num
end

; Report amount of links between activists
to-report num-connections-activist
  let num 0

  let nodes list-activist-persons

  foreach sort nodes [ n ->
    ask n [
      let followees in-following-neighbors with [ person-is-activist ]
      set num (num + count followees)
    ]
  ]

  report num
end

;; Report percentage of connection between different node types in relation to amount of links
to-report connections-percents [ follower_hater? followee_hater? ]
  report (num-connections follower_hater? followee_hater?) / (count followings)
end

; Report amount of reciprocal links between specific groups
to-report num-reciprocal-connections [ haters? ]
  let num 0

  let nodes []
  ifelse haters?
  [ set nodes list-hateful-persons ]
  [ set nodes list-normal-persons ]

  foreach sort nodes [ n ->
    ask n [
      let followees []
      ifelse haters?
      [ set followees in-following-neighbors with [ person-is-hater ] ]
      [ set followees in-following-neighbors with [ person-is-normal ] ]

      set num (num + count followees with [person-is-reciprocally-connected n])
    ]
  ]

  report num
end


; Report amount of reciprocal links between activist
to-report num-reciprocal-connections-activist
  let num 0

  let nodes list-activist-persons

  foreach sort nodes [ n ->
    ask n [
      let followees in-following-neighbors with [ person-is-activist ]
      set num (num + count followees with [person-is-reciprocally-connected n])
    ]
  ]

  report num
end

to-report person-is-reciprocally-connected [ follower ]
  report in-following-neighbor? follower
end

; Report amount of reciprocal links between specific groups
to-report reciprocal-connections-percents [ haters? ]
  let base (num-connections haters? haters?)
  ifelse base < 1
  [ report 0 ]
  [ report (num-reciprocal-connections haters?) / base ]
end


; Report amount of reciprocal links between specific groups
to-report reciprocal-connections-percents-activist
  let base (num-connections-activist)
  ifelse base < 1
  [ report 0 ]
  [ report (num-reciprocal-connections-activist) / base ]
end

; Reports density of connections between types of users, which means amount of connections diveded by amount of users
to-report connection-density [ between_haters? ]
  let num_connections []
  let ns []

  ifelse between_haters?
  [
    set ns list-hateful-persons
    set num_connections sum [count out-following-neighbors with [ person-is-hater ]] of ns
  ]
  [
    set ns list-normal-persons
    set num_connections sum [count out-following-neighbors with [ person-is-normal ]] of ns
  ]

  let num_nodes count ns
  let num_potential_connections (num_nodes * (num_nodes - 1) / 2)
  ifelse num_nodes < 2
  [ report 0 ]
  [ report num_connections / num_potential_connections ]
end

to-report amount-communities
  nw:set-context persons links
  report length nw:louvain-communities
end

to-report num-hateful-persons
  report count list-hateful-persons
end

to-report num-normal-persons
  report count list-normal-persons
end

to-report num-activist-persons
  report count list-activist-persons
end

to-report list-hateful-persons
  report persons with [ person-is-hater ]
end

to-report list-normal-persons
  report persons with [ person-is-normal ]
end

to-report list-activist-persons
  report persons with [ person-is-activist ]
end

to-report percents-hateful-persons
  report 100 * num-hateful-persons / count persons
end

to-report percents-activist-persons
  report 100 * num-activist-persons / count persons
end

to-report num-hateful-posts
  report count list-hateful-posts
end

to-report num-normal-posts
  report count list-normal-posts
end

to-report percents-hateful-posts
  ifelse count posts > 0
  [ report count list-hateful-posts / count posts ]
  [ report 0 ]
end

to-report percents-normal-posts
  ifelse count posts > 0
  [ report count list-normal-posts / count posts ]
  [ report 0 ]
end

to-report percents-activist-posts
  ifelse count posts > 0
  [ report count list-activist-posts / count posts ]
  [ report 0 ]
end

to-report list-hateful-posts
  report posts with [ post-is-hater ]
end

to-report list-normal-posts
  report posts with [ post-is-normal ]
end

to-report list-activist-posts
  report posts with [ post-is-activist ]
end

to-report reposts-by-haters
  report percentage_reposts_hater
end

to-report reposts-by-normals
  report percentage_reposts_normal
end

to-report swap-to-hate
  report percents-hateful-persons >= 30
end

to-report stddev-hate-score-dist
  report (standard-deviation [t_hate_score] of persons)
end

to-report polarisation-factor
;  report percents-hateful-persons * stddev-hate-score-dist
  report (count persons with [t_hate_score >= 0.5]) / (count persons) * 100 * stddev-hate-score-dist
end

;; Return amount of posts
to-report smoothed-num-posts [ hater? ]
  let ps nobody
  ifelse hater?
  [ set ps list-hateful-posts ]
  [ set ps list-normal-posts ]

  let num_all_posts count posts
  if num_all_posts < 1
  [ set num_all_posts 1 ]

  let n count ps / num_all_posts * 100
  let smoothness 0.99
  ifelse hater?
  [
    set smoothed_num_posts_hater smoothness * smoothed_num_posts_hater + (1 - smoothness) * n
    report smoothed_num_posts_hater
  ]
  [
    set smoothed_num_posts_normal smoothness * smoothed_num_posts_normal + (1 - smoothness) * n
    report smoothed_num_posts_normal
  ]
end


;; Return amount of posts of activists
to-report smoothed-num-posts-activist
  let ps list-activist-posts

  let num_all_posts count posts
  if num_all_posts < 1
  [ set num_all_posts 1 ]

  let n count ps / num_all_posts * 100
  let smoothness 0.99
  set smoothed_num_posts_activist smoothness * smoothed_num_posts_activist + (1 - smoothness) * n
  report smoothed_num_posts_activist
end

;; Return smoothed mean path length of reposts
to-report smoothed-mean-path-length [ hater? ]
  let ps nobody
  ifelse hater?
  [ set ps list-hateful-posts ]
  [ set ps list-normal-posts ]

  let n 0
  if count ps > 0
  [ set n mean [t_repost_path_length] of ps ]

  let smoothness 0.99
  ifelse hater?
  [
    set smoothed_path_length_hater smoothness * smoothed_path_length_hater + (1 - smoothness) * n
    report smoothed_path_length_hater
  ]
  [
    set smoothed_path_length_normal smoothness * smoothed_path_length_normal + (1 - smoothness) * n
    report smoothed_path_length_normal
  ]
end

to-report smoothed-mean-path-length-activist
  let ps list-activist-posts

  let n 0
  if count ps > 0
  [ set n mean [t_repost_path_length] of ps ]

  let smoothness 0.99
  set smoothed_path_length_activist smoothness * smoothed_path_length_activist + (1 - smoothness) * n
  report smoothed_path_length_activist
end

to-report mean-path-length [hater?]
  let ps nobody
  ifelse hater?
  [ set ps list-hateful-posts ]
  [ set ps list-normal-posts ]

  ifelse count ps > 0
  [ report mean [t_repost_path_length] of ps ]
  [ report 0 ]
end

to-report mean-path-length-activist
  let ps list-activist-posts

  ifelse count ps > 0
  [ report mean [t_repost_path_length] of ps ]
  [ report 0 ]
end

;; Plot opinion acceptance function
to plot-opinion-acceptance-values []
  let interval 0.005

  ; Setup plot
  plot-pen-reset  ;; erase what we plotted before
  set-plot-x-range 0 1
  set-plot-pen-interval interval

  ; Get values to plot
  let values opinion-acceptance-values interval

  foreach values [ v -> plot v ]
end

;; Get opinion acceptance function values for plot
to-report opinion-acceptance-values [ interval ]
  let hate-scores (range 0 1 interval)
  report map opinon-acceptance-mapping hate-scores
end

to-report max-out-degree [hater?]
  let degrees []
  ifelse hater?
  [set degrees [count out-following-neighbors] of list-hateful-persons]
  [set degrees [count out-following-neighbors] of list-normal-persons]

  if length degrees < 1
  [ report 0 ]

  report (max degrees) + 1
end

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Layout ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; resize-nodes, change back and forth from size based on degree to a size of 1
to resize-nodes
  ifelse all? persons [size <= 1.5]
  [
    ;; a node is a circle with diameter determined by
    ;; the SIZE variable; using SQRT makes the circle's
    ;; area proportional to its degree
    ask persons [ set size sqrt count link-neighbors ]
  ]
  [
    ask persons [ set size 1.5 ]
  ]
end

to layout
  ;; the number 3 here is arbitrary; more repetitions slows down the
  ;; model, but too few gives poor layouts
  repeat 3 [
    ;; the more persons we have to fit into the same amount of space,
    ;; the smaller the inputs to layout-spring we'll need to use
    let factor sqrt count persons
    ;; numbers here are arbitrarily chosen for pleasing appearance
    layout-spring persons links (spring_const / factor) (spring_length / factor) (repulsion / factor)
    display  ;; for smooth animation
  ]
  ;; don't bump the edges of the world
  let x-offset max [xcor] of persons + min [xcor] of persons
  let y-offset max [ycor] of persons + min [ycor] of persons
  ;; big jumps look funny, so only adjust a little each time
  set x-offset limit-magnitude x-offset 0.1
  set y-offset limit-magnitude y-offset 0.1
  ask persons [
    setxy (xcor - x-offset / 2) (ycor - y-offset / 2)
  ]
end

to-report limit-magnitude [number limit]
  if number > limit [ report limit ]
  if number < (- limit) [ report (- limit) ]
  report number
end


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Utils ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

to export-graphml
  ; Set hater inicators accordingly
  ask persons [
    ifelse person-is-hater
    [ set t_is_hater? true ]
    [ set t_is_hater? false ]

  ]

  nw:set-context persons links
  nw:save-graphml "example.graphml"
end

;; Get opinion acceptance bounds per hate score of a user
;; This means the value for maximal difference to the opinion of another user/post,
;; which could influence the current user by application of an opinion diffusion model
to-report opinon-acceptance-mapping [ hate-score ]
  ; Scale factor scales the maximux diffence. It should not be above 2, however it can

  ;; Version 1
;  let scale-factor 1.6
;  report scale-factor * hate-score * (1 - hate-score)

  ;; Version 2
;  ifelse hate-score < 0.1 or hate-score > 0.9
;  [ report 0 ]
;  [ report 0.25 ]
;

;  if hate-score <= 0.5
;  [ report (hate-score - 0.1) * 0.2 + 0.1 ]
;  report (0.9 - hate-score) * 0.2 + 0.1

  ;; Version 3
;  if hate-score < 0.25 or hate-score > 0.75
;  [ report 0 ]
;

  ;; Version 4
;  if hate-score < 0.25 or hate-score > 0.75
;  [ report 0 ]

;  report 0.25
;  report 0.49

  if op_form = "rectangle" [
    ;; Version generic
    if hate-score < op_extreme or hate-score > 1 - op_extreme
    [ report 0 ]
    report op_high
  ]


  ; Triangular opinion bounds
  let point_left_x op_extreme
  let point_left_y 0
  let point_middle_x 0.5
  let point_middle_y op_high
  let point_right_x 1 - op_extreme
  let point_right_y 0

  if hate-score < point_left_x or hate-score > point_right_x
  [ report 0 ]

  if hate-score <= 0.5
  [
    let slope_left (point_middle_y - point_left_y) / (point_middle_x - point_left_x)
    report slope_left * (hate-score - op_extreme)
  ]
  if hate-score > 0.5
  [
    let slope_right (point_right_y - point_middle_y) / (point_right_x - point_middle_x)
    report slope_right * (hate-score - 1 + op_extreme)
  ]

end
@#$#@#$#@
GRAPHICS-WINDOW
343
13
945
616
-1
-1
4.91
1
10
1
1
1
0
0
0
1
-60
60
-60
60
1
1
1
ticks
60.0

BUTTON
12
48
220
83
NIL
setup
NIL
1
T
OBSERVER
NIL
S
NIL
NIL
1

BUTTON
119
89
220
124
NIL
go
T
1
T
OBSERVER
NIL
R
NIL
NIL
0

BUTTON
13
90
115
123
go-once
go
NIL
1
T
OBSERVER
NIL
G
NIL
NIL
0

SWITCH
230
50
330
83
plot?
plot?
1
1
-1000

SWITCH
9
410
218
443
layout?
layout?
1
1
-1000

MONITOR
230
90
330
135
# of nodes
count persons
3
1
11

BUTTON
114
372
217
405
redo layout
layout
T
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

BUTTON
9
372
108
406
resize nodes
resize-nodes
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
0

BUTTON
10
488
218
522
export to GraphML
export-graphml
NIL
1
T
OBSERVER
NIL
NIL
NIL
NIL
1

SLIDER
15
694
220
727
hate_score_dist_alpha
hate_score_dist_alpha
1
10
10.0
0.5
1
NIL
HORIZONTAL

TEXTBOX
24
625
174
643
NIL
12
0.0
1

TEXTBOX
17
667
244
697
Gamma distribuition params
12
0.0
1

SLIDER
15
729
220
762
hate_score_dist_lambda
hate_score_dist_lambda
5
25
25.0
0.25
1
NIL
HORIZONTAL

SLIDER
229
692
434
725
hate_score_hater
hate_score_hater
0.5
1
0.75
0.05
1
NIL
HORIZONTAL

TEXTBOX
230
670
422
700
Score for hateful user
12
0.0
1

TEXTBOX
687
668
873
698
Back-Follow probabilities
12
0.0
1

PLOT
232
769
439
889
Mean hate score
ticks
hate score
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "if not plot? [ stop ]\nplot mean-hate-score"

MONITOR
235
1019
438
1064
% of hateful users 
percents-hateful-persons
1
1
11

PLOT
17
768
225
888
Hate score distribution
hate score
nodes
0.0
1.0
0.0
100.0
true
false
"" ""
PENS
"default" 0.05 1 -16777216 true "" "if not plot? [ stop ]\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 0 1\nhistogram [t_hate_score] of persons\n"

PLOT
1178
815
1384
935
Followers of normals
NIL
NIL
0.0
10.0
0.0
10.0
false
false
"" ""
PENS
"normal" 1.0 1 -13345367 true "" "if not plot? [ stop ]\nlet degrees [count out-following-neighbors] of list-normal-persons\nlet max-degree max degrees\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 1 (max-degree + 1)  ;; + 1 to make room for the width of the last bar\nhistogram degrees"

PLOT
1178
940
1383
1060
Followers of normals [log]
NIL
NIL
0.0
0.3
0.0
0.3
true
false
"" ""
PENS
"default" 1.0 0 -13345367 true "" "if not plot? [ stop ]\nlet max-degree max [count out-following-neighbors] of list-normal-persons\n;; for this plot, the axes are logarithmic, so we can't\n;; use \"histogram-from\"; we have to plot the points\n;; ourselves one at a time\nplot-pen-reset  ;; erase what we plotted before\n;; the way we create the network there is never a zero degree node,\n;; so start plotting at degree one\nlet degree 1\nwhile [degree <= max-degree] [\n  let matches persons with [(count out-following-neighbors = degree) and (t_hate_score < hate_score_hater)]\n  if any? matches\n    [ plotxy log degree 10\n             log (count matches) 10 ]\n  set degree degree + 1\n]"

PLOT
1388
814
1595
934
Followers of haters
NIL
NIL
0.0
10.0
0.0
10.0
false
false
"" ""
PENS
"hater" 1.0 1 -5298144 true "" "if not plot? [ stop ]\nlet degrees [count out-following-neighbors] of list-hateful-persons\nif empty? degrees [ stop ]\nlet max-degree max degrees\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 1 (max-degree + 1)  ;; + 1 to make room for the width of the last bar\nhistogram degrees"

PLOT
965
815
1173
935
Mean follower
NIL
NIL
0.0
3.0
0.0
3.0
true
false
"" ""
PENS
"normal" 1.0 0 -13345367 true "" "if not plot? [ stop ]\nplot mean-following true false"
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot mean-following true true"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot mean-following-activist true"

CHOOSER
12
247
215
292
dynamics_until_ticks
dynamics_until_ticks
100 200 500 1000 1500 2000 2500 3000 3500 5000 6000 6500 10000 11000 20000 50000
11

PLOT
964
690
1171
810
Follower / Followee
NIL
NIL
0.0
3.0
0.0
1.0
true
false
"" ""
PENS
"normal" 1.0 0 -14070903 true "" "if not plot? [ stop ]\nplot mean-follower-followee false"
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot mean-follower-followee true"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot mean-follower-followee-activist"

CHOOSER
13
150
216
195
grow_until_size
grow_until_size
100 200 500 1000 1500 2000 2500 3000 3500 5000 6000 6500 10000 11000 20000 50000
11

PLOT
468
855
679
975
Mean follow prob.
NIL
NIL
0.0
10.0
0.0
1.0
true
true
"" ""
PENS
"N->N" 1.0 0 -13345367 true "" "if not plot? [ stop ]\nplot mean-follow-prob false false"
"H->H" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot mean-follow-prob true true"
"H->N" 1.0 0 -7500403 true "" "if not plot? [ stop ]\nplot mean-follow-prob true false"
"N->H" 1.0 0 -16777216 true "" "if not plot? [ stop ]\nplot mean-follow-prob false true"

SLIDER
1185
103
1437
136
p_publish_post_hater
p_publish_post_hater
0
1
1.0
0.05
1
NIL
HORIZONTAL

TEXTBOX
1189
45
1339
63
Posting robabilities
12
0.0
1

SLIDER
1184
64
1437
97
p_publish_post_normal
p_publish_post_normal
0
1
0.2
0.01
1
NIL
HORIZONTAL

SLIDER
1185
251
1443
284
p_normal_reposts_hater
p_normal_reposts_hater
0
0.50
0.15
0.01
1
NIL
HORIZONTAL

SLIDER
1183
179
1442
212
p_normal_reposts_normal
p_normal_reposts_normal
0
0.5
0.15
0.05
1
NIL
HORIZONTAL

SLIDER
1184
214
1442
247
p_hater_reposts_hater
p_hater_reposts_hater
0
0.5
0.45
0.05
1
NIL
HORIZONTAL

TEXTBOX
1188
145
1381
191
Probabilities of reposting content
12
0.0
1

PLOT
964
365
1173
485
% posts per tick
NIL
NIL
0.0
10.0
0.0
100.0
true
false
"" ""
PENS
"normal" 1.0 0 -13345367 true "" "if not plot? [ stop ]\nplot smoothed-num-posts false"
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot smoothed-num-posts true"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot smoothed-num-posts-activist"

PLOT
965
493
1175
613
Post path length
NIL
NIL
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"normal" 1.0 0 -13345367 false "" "if not plot? [ stop ]\nplot smoothed-mean-path-length false\n"
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot smoothed-mean-path-length true\n"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot smoothed-mean-path-length-activist\n"

SLIDER
1185
287
1442
320
p_hater_reposts_normal
p_hater_reposts_normal
0
0.15
0.05
0.01
1
NIL
HORIZONTAL

PLOT
960
180
1165
300
Opinion acceptance bounds for diffusion
hate score
max difference
0.0
1.0
0.0
0.5
true
false
"plot-opinion-acceptance-values" ""
PENS
"default" 1.0 0 -16777216 true "" ""

SWITCH
230
190
330
223
repost?
repost?
0
1
-1000

SLIDER
12
295
219
328
mixing_parameter
mixing_parameter
0.0
0.5
0.05
0.05
1
NIL
HORIZONTAL

SWITCH
230
153
330
186
diffuse?
diffuse?
0
1
-1000

SLIDER
224
370
257
520
spring_const
spring_const
1
10
4.0
1
1
NIL
VERTICAL

SLIDER
262
372
295
522
spring_length
spring_length
1
100
76.0
5
1
NIL
VERTICAL

SLIDER
300
370
333
520
repulsion
repulsion
1
30
23.0
1
1
NIL
VERTICAL

SLIDER
462
690
669
723
n_following_conn_normal
n_following_conn_normal
1
5
1.0
1
1
NIL
HORIZONTAL

SLIDER
464
727
670
760
n_following_conn_hater
n_following_conn_hater
1
10
2.0
1
1
NIL
HORIZONTAL

TEXTBOX
463
669
613
687
Connections on creation
12
0.0
1

PLOT
232
894
440
1014
% hateful/activist users
NIL
NIL
0.0
10.0
0.0
5.0
true
false
"" ""
PENS
"hateful" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot percents-hateful-persons"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot percents-activist-persons"

CHOOSER
13
199
216
244
dynamics_from_ticks
dynamics_from_ticks
0 100 200 500 1000 1500 2000 2500 3000 3500 5000 6000 6500 10000 11000 20000 50000
10

SWITCH
9
450
219
483
display_only_influence?
display_only_influence?
1
1
-1000

CHOOSER
959
117
1059
162
op_high
op_high
0.1 0.2 0.25 0.3 0.4 0.49 0.5
5

CHOOSER
1063
117
1163
162
op_extreme
op_extreme
0 0.01 0.1 0.25
1

CHOOSER
958
68
1163
113
op_form
op_form
"rectangle" "triangle"
1

PLOT
18
895
226
1015
StdDev hate score distributino
NIL
NIL
0.0
10.0
0.0
0.5
true
false
"" ""
PENS
"default" 1.0 0 -16777216 false "" "if not plot? [ stop ]\nplot stddev-hate-score-dist "

MONITOR
20
1019
224
1064
StdDev hate score distribution
stddev-hate-score-dist
3
1
11

TEXTBOX
963
47
1173
78
Opinion acceptance bounds
12
0.0
1

PLOT
1388
940
1595
1062
Followers of haters (log)
NIL
NIL
0.0
1.0
0.0
1.0
true
false
"" ""
PENS
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nlet max-degree max [count out-following-neighbors] of list-hateful-persons\n;; for this plot, the axes are logarithmic, so we can't\n;; use \"histogram-from\"; we have to plot the points\n;; ourselves one at a time\nplot-pen-reset  ;; erase what we plotted before\n;; the way we create the network there is never a zero degree node,\n;; so start plotting at degree one\nlet degree 1\nwhile [degree <= max-degree] [\n  let matches turtles with [(count out-following-neighbors = degree) and (t_hate_score >= hate_score_hater)]\n  if any? matches\n    [ plotxy log degree 10\n             log (count matches) 10 ]\n  set degree degree + 1\n]"

PLOT
688
855
892
975
Conn. density H / N
NIL
NIL
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"N-N" 1.0 0 -16777216 true "" "if not plot? [ stop ]\nplot connection-density true / connection-density false"

PLOT
468
980
679
1106
% edges
NIL
NIL
0.0
10.0
0.0
0.01
true
true
"" ""
PENS
"H->N" 1.0 0 -7500403 true "" "if not plot? [ stop ]\nplot connections-percents true false"
"N->H" 1.0 0 -16777216 true "" "if not plot? [ stop ]\nplot connections-percents false true"
"H->H" 1.0 0 -2674135 true "" "if not plot? [ stop ]\nplot connections-percents true true"

PLOT
688
983
892
1108
Reciprocal connections
NIL
NIL
0.0
10.0
0.0
1.0
true
false
"" ""
PENS
"N<->N" 1.0 0 -14070903 true "" "if not plot? [ stop ]\nplot reciprocal-connections-percents false"
"H<->H" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot reciprocal-connections-percents true"
"A<->A" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot reciprocal-connections-percents-activist"

SLIDER
689
769
941
802
p_normal_back_follows_normal
p_normal_back_follows_normal
0
1
0.8
0.05
1
NIL
HORIZONTAL

SLIDER
688
810
944
843
p_hater_back_follows_normal
p_hater_back_follows_normal
0
1
0.08
0.01
1
NIL
HORIZONTAL

SLIDER
687
728
941
761
p_normal_back_follows_hater
p_normal_back_follows_hater
0
1
0.4
0.05
1
NIL
HORIZONTAL

SLIDER
685
690
938
723
p_hater_back_follows_hater
p_hater_back_follows_hater
0
1
0.9
0.01
1
NIL
HORIZONTAL

SLIDER
465
765
669
798
p_hater_follows_hater
p_hater_follows_hater
0
1
0.9
0.01
1
NIL
HORIZONTAL

SLIDER
1184
403
1441
436
max_reposts_by_haters
max_reposts_by_haters
0
10
6.0
1
1
NIL
HORIZONTAL

SLIDER
1183
365
1441
398
max_reposts_by_normals
max_reposts_by_normals
0
10
2.0
1
1
NIL
HORIZONTAL

PLOT
964
939
1171
1059
Mean followee
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"normal" 1.0 0 -13345367 true "" "if not plot? [ stop ]\nplot mean-following false false"
"hater" 1.0 0 -5298144 true "" "if not plot? [ stop ]\nplot mean-following false true"
"activist" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot mean-following-activist false"

TEXTBOX
1189
339
1377
358
Repost constraints
12
0.0
1

TEXTBOX
1192
519
1380
542
Deferring hate posts\n
12
0.0
1

SLIDER
1188
540
1444
573
p_defer_hateful_post
p_defer_hateful_post
0
1
0.0
0.05
1
NIL
HORIZONTAL

SLIDER
1188
578
1445
611
p_repost_deferred_post
p_repost_deferred_post
0
1
0.5
0.05
1
NIL
HORIZONTAL

PLOT
1180
692
1384
812
Follower / Followee hater dist
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"hater" 0.5 1 -5298144 true "" "if not plot? [ stop ]\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 0 10\nhistogram [follower-followee] of list-hateful-persons"

PLOT
1390
692
1596
812
Follower / Followee normal dist
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"normal" 0.5 1 -14070903 true "" "if not plot? [ stop ]\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 0 10\nhistogram [follower-followee] of list-normal-persons"

TEXTBOX
963
15
1151
38
Opinion dynamics
14
0.0
1

TEXTBOX
15
343
203
366
Visualisation
2
0.0
1

TEXTBOX
14
14
202
37
Simulation control
14
0.0
1

TEXTBOX
17
635
287
678
Sampled hate score distribution
14
0.0
1

TEXTBOX
462
637
650
660
Static network growth
14
0.0
1

TEXTBOX
1190
490
1378
513
Countermeasure 2
14
0.0
1

TEXTBOX
1480
20
1668
43
Countemeasure 3
14
0.0
1

TEXTBOX
1476
186
1664
209
Network growth
12
0.0
1

SWITCH
1480
64
1749
97
activists_mode?
activists_mode?
0
1
-1000

SLIDER
1476
281
1753
314
n_following_conn_activist_additional
n_following_conn_activist_additional
0
10
2.0
1
1
NIL
HORIZONTAL

SLIDER
1476
321
1754
354
p_activist_back_follows_activist
p_activist_back_follows_activist
0
1
0.9
0.05
1
NIL
HORIZONTAL

SLIDER
1476
243
1753
276
p_convincing_to_become_activist
p_convincing_to_become_activist
0
0.5
0.01
0.005
1
NIL
HORIZONTAL

TEXTBOX
1477
368
1665
391
Opinion dynamics
12
0.0
1

SLIDER
1476
394
1755
427
p_publish_post_activist
p_publish_post_activist
0
1
1.0
0.1
1
NIL
HORIZONTAL

SLIDER
1477
435
1757
468
p_activist_reposts_activist
p_activist_reposts_activist
0
1
0.45
0.05
1
NIL
HORIZONTAL

SLIDER
1477
474
1756
507
p_normal_reposts_activist
p_normal_reposts_activist
0
1
0.15
0.05
1
NIL
HORIZONTAL

SLIDER
1477
512
1759
545
max_reposts_by_activists
max_reposts_by_activists
0
10
6.0
1
1
NIL
HORIZONTAL

SLIDER
1477
144
1749
177
hate_score_potential_activist
hate_score_potential_activist
0
0.25
0.25
0.05
1
NIL
HORIZONTAL

PLOT
1600
813
1799
933
Followers of activists
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 1.0 1 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nlet degrees [count out-following-neighbors] of list-activist-persons\nlet max-degree max degrees\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 1 (max-degree + 1)  ;; + 1 to make room for the width of the last bar\nhistogram degrees"

PLOT
1600
940
1800
1063
Followers of activists (log)
NIL
NIL
0.0
1.0
0.0
1.0
true
false
"" ""
PENS
"default" 1.0 0 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nlet max-degree max [count out-following-neighbors] of list-activist-persons\n;; for this plot, the axes are logarithmic, so we can't\n;; use \"histogram-from\"; we have to plot the points\n;; ourselves one at a time\nplot-pen-reset  ;; erase what we plotted before\n;; the way we create the network there is never a zero degree node,\n;; so start plotting at degree one\nlet degree 1\nwhile [degree <= max-degree] [\n  let matches turtles with [(count out-following-neighbors = degree) and t_is_activist?]\n  if any? matches\n    [ plotxy log degree 10\n             log (count matches) 10 ]\n  set degree degree + 1\n]"

PLOT
1600
691
1800
811
Follower / Followee activists
NIL
NIL
0.0
10.0
0.0
10.0
true
false
"" ""
PENS
"default" 0.5 1 -16777216 true "" "if not activists_mode? or not plot? [ stop ]\nplot-pen-reset  ;; erase what we plotted before\nset-plot-x-range 0 10\nhistogram [follower-followee] of list-activist-persons"

MONITOR
235
1069
436
1114
% of activist users
percents-activist-persons
17
1
11

SWITCH
1480
101
1750
134
stubborn_activists?
stubborn_activists?
0
1
-1000

SWITCH
1476
204
1754
237
select_activist_by_influence?
select_activist_by_influence?
0
1
-1000

@#$#@#$#@
## WHAT IS IT?

In some networks, a few "hubs" have lots of connections, while everybody else only has a few.  This model shows one way such networks can arise.

Such networks can be found in a surprisingly large range of real world situations, ranging from the connections between websites to the collaborations between actors.

This model generates these networks by a process of "preferential attachment", in which new network members prefer to make a connection to the more popular existing members.

## HOW IT WORKS

The model starts with two nodes connected by an edge.

At each step, a new node is added.  A new node picks an existing node to connect to randomly, but with some bias.  More specifically, a node's chance of being selected is directly proportional to the number of connections it already has, or its "degree." This is the mechanism which is called "preferential attachment."

## HOW TO USE IT

Pressing the GO ONCE button adds one new node.  To continuously add nodes, press GO.

The LAYOUT? switch controls whether or not the layout procedure is run.  This procedure attempts to move the nodes around to make the structure of the network easier to see.

The PLOT? switch turns off the plots which speeds up the model.

The RESIZE-NODES button will make all of the nodes take on a size representative of their degree distribution.  If you press it again the nodes will return to equal size.

If you want the model to run faster, you can turn off the LAYOUT? and PLOT? switches and/or freeze the view (using the on/off button in the control strip over the view). The LAYOUT? switch has the greatest effect on the speed of the model.

If you have LAYOUT? switched off, and then want the network to have a more appealing layout, press the REDO-LAYOUT button which will run the layout-step procedure until you press the button again. You can press REDO-LAYOUT at any time even if you had LAYOUT? switched on and it will try to make the network easier to see.

## THINGS TO NOTICE

The networks that result from running this model are often called "scale-free" or "power law" networks. These are networks in which the distribution of the number of connections of each node is not a normal distribution --- instead it follows what is a called a power law distribution.  Power law distributions are different from normal distributions in that they do not have a peak at the average, and they are more likely to contain extreme values (see Albert & Barabási 2002 for a further description of the frequency and significance of scale-free networks).  Barabási and Albert originally described this mechanism for creating networks, but there are other mechanisms of creating scale-free networks and so the networks created by the mechanism implemented in this model are referred to as Barabási scale-free networks.

You can see the degree distribution of the network in this model by looking at the plots. The top plot is a histogram of the degree of each node.  The bottom plot shows the same data, but both axes are on a logarithmic scale.  When degree distribution follows a power law, it appears as a straight line on the log-log plot.  One simple way to think about power laws is that if there is one node with a degree distribution of 1000, then there will be ten nodes with a degree distribution of 100, and 100 nodes with a degree distribution of 10.

## THINGS TO TRY

Let the model run a little while.  How many nodes are "hubs", that is, have many connections?  How many have only a few?  Does some low degree node ever become a hub?  How often?

Turn off the LAYOUT? switch and freeze the view to speed up the model, then allow a large network to form.  What is the shape of the histogram in the top plot?  What do you see in log-log plot? Notice that the log-log plot is only a straight line for a limited range of values.  Why is this?  Does the degree to which the log-log plot resembles a straight line grow as you add more nodes to the network?

## EXTENDING THE MODEL

Assign an additional attribute to each node.  Make the probability of attachment depend on this new attribute as well as on degree.  (A bias slider could control how much the attribute influences the decision.)

Can the layout algorithm be improved?  Perhaps nodes from different hubs could repel each other more strongly than nodes from the same hub, in order to encourage the hubs to be physically separate in the layout.

## NETWORK CONCEPTS

There are many ways to graphically display networks.  This model uses a common "spring" method where the movement of a node at each time step is the net result of "spring" forces that pulls connected nodes together and repulsion forces that push all the nodes away from each other.  This code is in the `layout-step` procedure. You can force this code to execute any time by pressing the REDO LAYOUT button, and pressing it again when you are happy with the layout.

## NETLOGO FEATURES

Nodes are turtle agents and edges are link agents. The model uses the ONE-OF primitive to chose a random link and the BOTH-ENDS primitive to select the two nodes attached to that link.

The `layout-spring` primitive places the nodes, as if the edges are springs and the nodes are repelling each other.

Though it is not used in this model, there exists a network extension for NetLogo that comes bundled with NetLogo, that has many more network primitives.

## RELATED MODELS

See other models in the Networks section of the Models Library, such as Giant Component.

See also Network Example, in the Code Examples section.

## CREDITS AND REFERENCES

This model is based on:
Albert-László Barabási. Linked: The New Science of Networks, Perseus Publishing, Cambridge, Massachusetts, pages 79-92.

For a more technical treatment, see:
Albert-László Barabási & Reka Albert. Emergence of Scaling in Random Networks, Science, Vol 286, Issue 5439, 15 October 1999, pages 509-512.

Barabási's webpage has additional information at: http://www.barabasi.com/

The layout algorithm is based on the Fruchterman-Reingold layout algorithm.  More information about this algorithm can be obtained at: http://cs.brown.edu/people/rtamassi/gdhandbook/chapters/force-directed.pdf.

For a model similar to the one described in the first suggested extension, please consult:
W. Brian Arthur, "Urban Systems and Historical Path-Dependence", Chapt. 4 in Urban systems and Infrastructure, J. Ausubel and R. Herman (eds.), National Academy of Sciences, Washington, D.C., 1988.

## HOW TO CITE

If you mention this model or the NetLogo software in a publication, we ask that you include the citations below.

For the model itself:

* Wilensky, U. (2005).  NetLogo Preferential Attachment model.  http://ccl.northwestern.edu/netlogo/models/PreferentialAttachment.  Center for Connected Learning and Computer-Based Modeling, Northwestern University, Evanston, IL.

Please cite the NetLogo software as:

* Wilensky, U. (1999). NetLogo. http://ccl.northwestern.edu/netlogo/. Center for Connected Learning and Computer-Based Modeling, Northwestern University, Evanston, IL.

## COPYRIGHT AND LICENSE

Copyright 2005 Uri Wilensky.

![CC BY-NC-SA 3.0](http://ccl.northwestern.edu/images/creativecommons/byncsa.png)

This work is licensed under the Creative Commons Attribution-NonCommercial-ShareAlike 3.0 License.  To view a copy of this license, visit https://creativecommons.org/licenses/by-nc-sa/3.0/ or send a letter to Creative Commons, 559 Nathan Abbott Way, Stanford, California 94305, USA.

Commercial licenses are also available. To inquire about commercial licenses, please contact Uri Wilensky at uri@northwestern.edu.

<!-- 2005 -->
@#$#@#$#@
default
true
0
Polygon -7500403 true true 150 5 40 250 150 205 260 250

airplane
true
0
Polygon -7500403 true true 150 0 135 15 120 60 120 105 15 165 15 195 120 180 135 240 105 270 120 285 150 270 180 285 210 270 165 240 180 180 285 195 285 165 180 105 180 60 165 15

arrow
true
0
Polygon -7500403 true true 150 0 0 150 105 150 105 293 195 293 195 150 300 150

box
false
0
Polygon -7500403 true true 150 285 285 225 285 75 150 135
Polygon -7500403 true true 150 135 15 75 150 15 285 75
Polygon -7500403 true true 15 75 15 225 150 285 150 135
Line -16777216 false 150 285 150 135
Line -16777216 false 150 135 15 75
Line -16777216 false 150 135 285 75

bug
true
0
Circle -7500403 true true 96 182 108
Circle -7500403 true true 110 127 80
Circle -7500403 true true 110 75 80
Line -7500403 true 150 100 80 30
Line -7500403 true 150 100 220 30

butterfly
true
0
Polygon -7500403 true true 150 165 209 199 225 225 225 255 195 270 165 255 150 240
Polygon -7500403 true true 150 165 89 198 75 225 75 255 105 270 135 255 150 240
Polygon -7500403 true true 139 148 100 105 55 90 25 90 10 105 10 135 25 180 40 195 85 194 139 163
Polygon -7500403 true true 162 150 200 105 245 90 275 90 290 105 290 135 275 180 260 195 215 195 162 165
Polygon -16777216 true false 150 255 135 225 120 150 135 120 150 105 165 120 180 150 165 225
Circle -16777216 true false 135 90 30
Line -16777216 false 150 105 195 60
Line -16777216 false 150 105 105 60

car
false
0
Polygon -7500403 true true 300 180 279 164 261 144 240 135 226 132 213 106 203 84 185 63 159 50 135 50 75 60 0 150 0 165 0 225 300 225 300 180
Circle -16777216 true false 180 180 90
Circle -16777216 true false 30 180 90
Polygon -16777216 true false 162 80 132 78 134 135 209 135 194 105 189 96 180 89
Circle -7500403 true true 47 195 58
Circle -7500403 true true 195 195 58

circle
false
0
Circle -7500403 true true 0 0 300

circle 2
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240

cow
false
0
Polygon -7500403 true true 200 193 197 249 179 249 177 196 166 187 140 189 93 191 78 179 72 211 49 209 48 181 37 149 25 120 25 89 45 72 103 84 179 75 198 76 252 64 272 81 293 103 285 121 255 121 242 118 224 167
Polygon -7500403 true true 73 210 86 251 62 249 48 208
Polygon -7500403 true true 25 114 16 195 9 204 23 213 25 200 39 123

cylinder
false
0
Circle -7500403 true true 0 0 300

dot
false
0
Circle -7500403 true true 90 90 120

face happy
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 255 90 239 62 213 47 191 67 179 90 203 109 218 150 225 192 218 210 203 227 181 251 194 236 217 212 240

face neutral
false
0
Circle -7500403 true true 8 7 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Rectangle -16777216 true false 60 195 240 225

face sad
false
0
Circle -7500403 true true 8 8 285
Circle -16777216 true false 60 75 60
Circle -16777216 true false 180 75 60
Polygon -16777216 true false 150 168 90 184 62 210 47 232 67 244 90 220 109 205 150 198 192 205 210 220 227 242 251 229 236 206 212 183

fish
false
0
Polygon -1 true false 44 131 21 87 15 86 0 120 15 150 0 180 13 214 20 212 45 166
Polygon -1 true false 135 195 119 235 95 218 76 210 46 204 60 165
Polygon -1 true false 75 45 83 77 71 103 86 114 166 78 135 60
Polygon -7500403 true true 30 136 151 77 226 81 280 119 292 146 292 160 287 170 270 195 195 210 151 212 30 166
Circle -16777216 true false 215 106 30

flag
false
0
Rectangle -7500403 true true 60 15 75 300
Polygon -7500403 true true 90 150 270 90 90 30
Line -7500403 true 75 135 90 135
Line -7500403 true 75 45 90 45

flower
false
0
Polygon -10899396 true false 135 120 165 165 180 210 180 240 150 300 165 300 195 240 195 195 165 135
Circle -7500403 true true 85 132 38
Circle -7500403 true true 130 147 38
Circle -7500403 true true 192 85 38
Circle -7500403 true true 85 40 38
Circle -7500403 true true 177 40 38
Circle -7500403 true true 177 132 38
Circle -7500403 true true 70 85 38
Circle -7500403 true true 130 25 38
Circle -7500403 true true 96 51 108
Circle -16777216 true false 113 68 74
Polygon -10899396 true false 189 233 219 188 249 173 279 188 234 218
Polygon -10899396 true false 180 255 150 210 105 210 75 240 135 240

house
false
0
Rectangle -7500403 true true 45 120 255 285
Rectangle -16777216 true false 120 210 180 285
Polygon -7500403 true true 15 120 150 15 285 120
Line -16777216 false 30 120 270 120

leaf
false
0
Polygon -7500403 true true 150 210 135 195 120 210 60 210 30 195 60 180 60 165 15 135 30 120 15 105 40 104 45 90 60 90 90 105 105 120 120 120 105 60 120 60 135 30 150 15 165 30 180 60 195 60 180 120 195 120 210 105 240 90 255 90 263 104 285 105 270 120 285 135 240 165 240 180 270 195 240 210 180 210 165 195
Polygon -7500403 true true 135 195 135 240 120 255 105 255 105 285 135 285 165 240 165 195

line
true
0
Line -7500403 true 150 0 150 300

line half
true
0
Line -7500403 true 150 0 150 150

pentagon
false
0
Polygon -7500403 true true 150 15 15 120 60 285 240 285 285 120

person
false
0
Circle -7500403 true true 110 5 80
Polygon -7500403 true true 105 90 120 195 90 285 105 300 135 300 150 225 165 300 195 300 210 285 180 195 195 90
Rectangle -7500403 true true 127 79 172 94
Polygon -7500403 true true 195 90 240 150 225 180 165 105
Polygon -7500403 true true 105 90 60 150 75 180 135 105

plant
false
0
Rectangle -7500403 true true 135 90 165 300
Polygon -7500403 true true 135 255 90 210 45 195 75 255 135 285
Polygon -7500403 true true 165 255 210 210 255 195 225 255 165 285
Polygon -7500403 true true 135 180 90 135 45 120 75 180 135 210
Polygon -7500403 true true 165 180 165 210 225 180 255 120 210 135
Polygon -7500403 true true 135 105 90 60 45 45 75 105 135 135
Polygon -7500403 true true 165 105 165 135 225 105 255 45 210 60
Polygon -7500403 true true 135 90 120 45 150 15 180 45 165 90

square
false
0
Rectangle -7500403 true true 30 30 270 270

square 2
false
0
Rectangle -7500403 true true 30 30 270 270
Rectangle -16777216 true false 60 60 240 240

star
false
0
Polygon -7500403 true true 151 1 185 108 298 108 207 175 242 282 151 216 59 282 94 175 3 108 116 108

target
false
0
Circle -7500403 true true 0 0 300
Circle -16777216 true false 30 30 240
Circle -7500403 true true 60 60 180
Circle -16777216 true false 90 90 120
Circle -7500403 true true 120 120 60

tree
false
0
Circle -7500403 true true 118 3 94
Rectangle -6459832 true false 120 195 180 300
Circle -7500403 true true 65 21 108
Circle -7500403 true true 116 41 127
Circle -7500403 true true 45 90 120
Circle -7500403 true true 104 74 152

triangle
false
0
Polygon -7500403 true true 150 30 15 255 285 255

triangle 2
false
0
Polygon -7500403 true true 150 30 15 255 285 255
Polygon -16777216 true false 151 99 225 223 75 224

truck
false
0
Rectangle -7500403 true true 4 45 195 187
Polygon -7500403 true true 296 193 296 150 259 134 244 104 208 104 207 194
Rectangle -1 true false 195 60 195 105
Polygon -16777216 true false 238 112 252 141 219 141 218 112
Circle -16777216 true false 234 174 42
Rectangle -7500403 true true 181 185 214 194
Circle -16777216 true false 144 174 42
Circle -16777216 true false 24 174 42
Circle -7500403 false true 24 174 42
Circle -7500403 false true 144 174 42
Circle -7500403 false true 234 174 42

turtle
true
0
Polygon -10899396 true false 215 204 240 233 246 254 228 266 215 252 193 210
Polygon -10899396 true false 195 90 225 75 245 75 260 89 269 108 261 124 240 105 225 105 210 105
Polygon -10899396 true false 105 90 75 75 55 75 40 89 31 108 39 124 60 105 75 105 90 105
Polygon -10899396 true false 132 85 134 64 107 51 108 17 150 2 192 18 192 52 169 65 172 87
Polygon -10899396 true false 85 204 60 233 54 254 72 266 85 252 107 210
Polygon -7500403 true true 119 75 179 75 209 101 224 135 220 225 175 261 128 261 81 224 74 135 88 99

wheel
false
0
Circle -7500403 true true 3 3 294
Circle -16777216 true false 30 30 240
Line -7500403 true 150 285 150 15
Line -7500403 true 15 150 285 150
Circle -7500403 true true 120 120 60
Line -7500403 true 216 40 79 269
Line -7500403 true 40 84 269 221
Line -7500403 true 40 216 269 79
Line -7500403 true 84 40 221 269

x
false
0
Polygon -7500403 true true 270 75 225 30 30 225 75 270
Polygon -7500403 true true 30 75 75 30 270 225 225 270
@#$#@#$#@
NetLogo 6.2.0
@#$#@#$#@
set layout? false
set plot? false
setup repeat 300 [ go ]
repeat 100 [ layout ]
@#$#@#$#@
@#$#@#$#@
<experiments>
  <experiment name="high_hater_follow_probs_and_normal_reposts_hater--&gt;num_haters" repetitions="50" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>hateful-node-percents</metric>
    <metric>plot-smoothed-num-posts false</metric>
    <metric>plot-smoothed-num-posts true</metric>
    <metric>plot-smoothed-mean-path-length false</metric>
    <metric>plot-smoothed-mean-path-length true</metric>
    <metric>swap-to-hate</metric>
    <metric>polarisation-factor</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffusion_factor">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_normal_reposts_hater" first="0.01" step="0.02" last="0.5"/>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.03"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;rectangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.65"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_hater">
      <value value="0.35"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="high_hater_follow_probs_and_diff_acceptance--&gt;swap_to_hate" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffusion_factor">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.13"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.03"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.1"/>
      <value value="0.2"/>
      <value value="0.3"/>
      <value value="0.4"/>
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.65"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_hater">
      <value value="0.35"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="high_hater_follow_probs_repost--&gt;pollarisation" repetitions="50" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <metric>hateful-node-percents</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>polarisation-factor</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffusion_factor">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.13"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.03"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.65"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_hater">
      <value value="0.35"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="high_hater_follow_probs_and_normal_follows_normal--&gt;num_haters" repetitions="50" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>hateful-node-percents</metric>
    <metric>plot-smoothed-num-posts false</metric>
    <metric>plot-smoothed-num-posts true</metric>
    <metric>plot-smoothed-mean-path-length false</metric>
    <metric>plot-smoothed-mean-path-length true</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffusion_factor">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.13"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.03"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;rectangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_follows_normal">
      <value value="0.8"/>
      <value value="0.85"/>
      <value value="0.9"/>
      <value value="0.95"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.65"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_hater">
      <value value="0.35"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="high_hater_follow_probs_and_normal_reposts_hater--&gt;num_haters_triangle" repetitions="50" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>hateful-node-percents</metric>
    <metric>plot-smoothed-num-posts false</metric>
    <metric>plot-smoothed-num-posts true</metric>
    <metric>plot-smoothed-mean-path-length false</metric>
    <metric>plot-smoothed-mean-path-length true</metric>
    <metric>swap-to-hate</metric>
    <metric>polarisation-factor</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffusion_factor">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_normal_reposts_hater" first="0.01" step="0.02" last="0.5"/>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.03"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.65"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_back_follows_hater">
      <value value="0.35"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_network_growth" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>swap-to-hate</metric>
    <metric>polarisation-factor</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="20000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="20000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="20000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_network_growth_hater_to_hater_0.1" repetitions="30" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>hateful-persons-percents</metric>
    <metric>smoothed-num-posts false</metric>
    <metric>smoothed-num-posts true</metric>
    <metric>smoothed-mean-path-length false</metric>
    <metric>smoothed-mean-path-length true</metric>
    <metric>swap-to-hate</metric>
    <metric>polarisation-factor</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_0_1000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_500_1500" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_5000_6000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_1000_2000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_2000_3000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_diffusion_10000_11000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_0_1000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_500_1500" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_1000_2000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_2000_3000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_5000_6000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_baseline_reposts_10000_11000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="normal_reposts_hater_0_1000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_normal_reposts_hater" first="0.01" step="0.02" last="0.5"/>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="normal_reposts_hater_1000_2000" repetitions="50" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_normal_reposts_hater" first="0.01" step="0.02" last="0.5"/>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_0_1000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0" step="0.1" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_500_1500" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>mean-hate-score</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0" step="0.1" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_1000_2000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>mean-hate-score</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0.1" step="0.2" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_2000_3000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>mean-hate-score</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0.1" step="0.2" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_5000_6000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>mean-hate-score</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0.1" step="0.2" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_defer_10000_11000" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>mean-hate-score</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="10000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="11000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <steppedValueSet variable="p_defer_hateful_post" first="0.1" step="0.2" last="0.9"/>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_0_1000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="8.75"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_0_1000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="13.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_0_1000-6" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="17.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_0_1000-8" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_500_1500-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="8.75"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_500_1500-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="13.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_500_1500-6" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="17.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_500_1500-8" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_1000_2000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="8.75"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_1000_2000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="13.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_1000_2000-6" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="17.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_1000_2000-8" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_2000_3000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="8.75"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_2000_3000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="13.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_2000_3000-6" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="17.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_2000_3000-8" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_5000_6000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="8.75"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_5000_6000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="13.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_5000_6000-6" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="17.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_5000_6000-8" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_0_1000-8_a" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_1000_2000-8_a" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_500_1500-8_a" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_2000_3000-8_a" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_education_5000_6000-8_a" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="21.25"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_0_1000-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_0_1000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_0_1000-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_0_1000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_1500-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_1500-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_1500-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_1500-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="1500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2000-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2000-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-1" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-2" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-3" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-4" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-1-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-1-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-1-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-1-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-4-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-4-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-4-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-4-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_500_2000-2-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_1000_2500-2-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="1000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="2500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_2000_3500-2-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="2000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="3500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
  <experiment name="validate_counter_activists_5000_6500-2-pref" repetitions="100" runMetricsEveryStep="false">
    <setup>setup</setup>
    <go>go</go>
    <exitCondition>swap-to-hate</exitCondition>
    <metric>mean-follow-prob false false</metric>
    <metric>mean-follow-prob true true</metric>
    <metric>connection-density true</metric>
    <metric>connection-density false</metric>
    <metric>connections-percents true false</metric>
    <metric>connections-percents false true</metric>
    <metric>reciprocal-connections-percents false</metric>
    <metric>reciprocal-connections-percents true</metric>
    <metric>mean-follower-followee false</metric>
    <metric>mean-follower-followee true</metric>
    <metric>max-out-degree false</metric>
    <metric>max-out-degree true</metric>
    <metric>mean-following true false</metric>
    <metric>mean-following true true</metric>
    <metric>mean-following false false</metric>
    <metric>mean-following false true</metric>
    <metric>percents-persons-with-degree true true 0</metric>
    <metric>percents-persons-with-degree true true 1</metric>
    <metric>percents-persons-with-degree false true 0</metric>
    <metric>percents-persons-with-degree false true 1</metric>
    <metric>percents-hateful-persons</metric>
    <metric>percents-hateful-posts</metric>
    <metric>mean-path-length false</metric>
    <metric>mean-path-length true</metric>
    <metric>stddev-hate-score-dist</metric>
    <metric>mean-hate-score</metric>
    <metric>reposts-by-haters</metric>
    <metric>reposts-by-normals</metric>
    <metric>swap-to-hate</metric>
    <metric>percents-activist-persons</metric>
    <metric>mean-path-length-activist</metric>
    <metric>percents-activist-posts</metric>
    <enumeratedValueSet variable="plot?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="layout?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="diffuse?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="repost?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="grow_until_size">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_from_ticks">
      <value value="5000"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="dynamics_until_ticks">
      <value value="6500"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="mixing_parameter">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_form">
      <value value="&quot;triangle&quot;"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_extreme">
      <value value="0.01"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="op_high">
      <value value="0.49"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_normal">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_hater">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_hater">
      <value value="0.4"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_hater">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_back_follows_normal">
      <value value="0.8"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_back_follows_normal">
      <value value="0.08"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_hater">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_normal">
      <value value="0.2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_normal">
      <value value="0.05"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_hater_reposts_hater">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_hater">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_normal">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_normals">
      <value value="2"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_haters">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_hater">
      <value value="0.75"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_alpha">
      <value value="10"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="hate_score_dist_lambda">
      <value value="25"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_defer_hateful_post">
      <value value="0"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_repost_deferred_post">
      <value value="0.5"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="activists_mode?">
      <value value="true"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_back_follows_activist">
      <value value="0.9"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_publish_post_activist">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_activist_reposts_activist">
      <value value="0.45"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_normal_reposts_activist">
      <value value="0.15"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="max_reposts_by_activists">
      <value value="6"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="p_convincing_to_become_activist">
      <value value="0.04"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="n_following_conn_activist_additional">
      <value value="1"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="stubborn_activists?">
      <value value="false"/>
    </enumeratedValueSet>
    <enumeratedValueSet variable="select_activist_by_influence?">
      <value value="true"/>
    </enumeratedValueSet>
  </experiment>
</experiments>
@#$#@#$#@
@#$#@#$#@
default
0.0
-0.2 0 0.0 1.0
0.0 1 1.0 0.0
0.2 0 0.0 1.0
link direction
true
0
Line -7500403 true 150 150 90 180
Line -7500403 true 150 150 210 180
@#$#@#$#@
0
@#$#@#$#@
