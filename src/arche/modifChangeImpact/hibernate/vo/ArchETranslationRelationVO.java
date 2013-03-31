/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate.vo;

/**
 * VO class that represents a mapping relationship between a scenario 
 * (ArchEScenarioVO) and a responsibility (ArchEResponsibilityVO). 
 * <p>
 * These relations are created/manipulated by the ArchE core, so that each 
 * external reasoning framework should only restore them from the database.
 * <p>
 * This is a core concept (relation) that should not be extended by 
 * reasoning frameworks
 * 
 * @author Hyunwoo Kim
 */

import edu.cmu.sei.arche.external.data.ArchEVersion;

public class ArchETranslationRelationVO extends ArchERelationVO { 

	private static final long serialVersionUID = 1L;
	
	private String parentType; 			 // This value is always 'Scenario'
	private ArchEScenarioVO parent;		 // Scenario
	private ArchEResponsibilityVO child; // Responsibility 

	public ArchETranslationRelationVO() {
		super();
		parentType = "Scenario";
		parent = null;
		child = null;
	}
	
	public ArchETranslationRelationVO(ArchEVersion version){
		super(version);
		parentType = "Scenario";
		parent = null;
		child = null;
	}

	public String getParentType() {
		return this.parentType;
	}

	public void setParentType(String parentType) {
		this.parentType = parentType;
	}

	public ArchEScenarioVO getParent() {
		return this.parent;
	}

	public void setParent(ArchEScenarioVO parent) {
		this.parent = parent;
		if(parent != null)
			this.parentFact = parent.getFactId();
	}

	public ArchEResponsibilityVO getChild() {
		return this.child;
	}

	public void setChild(ArchEResponsibilityVO child) {
		this.child = child;
		if(child != null)
			this.childFact = child.getFactId();
	}

}
