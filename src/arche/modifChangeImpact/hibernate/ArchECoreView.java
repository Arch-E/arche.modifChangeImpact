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

package arche.modifChangeImpact.hibernate;

/**
 * A partial implementation of a default architectural view. The reasoning framework
 * developer must create appropriate subclasses, and then provide the details of how 
 * his/her view is persisted in the database.
 * 
 * @author Hyunwoo Kim
 */

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.hibernate.HibernateException;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchEDesignElement;
import edu.cmu.sei.arche.external.data.ArchEDesignRelation;
import edu.cmu.sei.arche.external.data.ArchEView;

public abstract class ArchECoreView implements ArchEView{
	
	protected ArchEArchitecture parent;
	protected ArchEVersionVO version;
	
	private List<ArchEDesignElement> removedViewElementVOs = null;
	private List<ArchEDesignRelation> removedViewRelationVOs = null;
	
	public ArchECoreView(ArchEArchitecture parent) {		
		this.parent = parent;
		this.version = (ArchEVersionVO)parent.getCurrentVersion();
		
		removedViewElementVOs = new ArrayList<ArchEDesignElement>();
		removedViewRelationVOs = new ArrayList<ArchEDesignRelation>();		
	}
	
	public void deleteDesignElement(ArchEDesignElement element){
		removedViewElementVOs.add(element);
	}

	public void deleteDesignRelation(ArchEDesignRelation relation){
		removedViewRelationVOs.add(relation);
	}
	
	public ArchEArchitecture getParent(){
		return parent;
	}
	
	public List<ArchEDesignElement> getDesignElements() {
		return (null);
	}
	
	public List<ArchEDesignRelation> getDesignRelations() {
		return (null);
	}
	
	public abstract void restore() throws ArchEException;
	
	public void save() throws ArchEException{
		// Note: if this method is overridden, then it should be called by the
		// subclass as super.save() before executing other statements in the method
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				for (Iterator<ArchEDesignElement> it = removedViewElementVOs.iterator(); it.hasNext();)
					openSession.delete(it.next());
				
				for (Iterator<ArchEDesignRelation> it = removedViewRelationVOs.iterator(); it.hasNext();)
					openSession.delete(it.next());				
			
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}				
	}
	
	public abstract void saveAs(ArchEVersionVO newVersion) throws ArchEException;
	
	// TODO: Should I do the same thing here than when saving the view 
	// (i.e., deletion of "removed" VOs)?
	public abstract void delete() throws ArchEException;
	
}
